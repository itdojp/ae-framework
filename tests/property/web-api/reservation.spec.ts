import fc from 'fast-check';
import { beforeAll, afterAll, describe, it, expect } from 'vitest';
import { buildApp } from '../../../src/web-api/app';
import { reservationArb, insufficientArb, defaultRuns } from './fast-check.config';

// property: idempotency and non-negative stock for reservations
// test:property:webapi で実行される

describe('property: web api reservations', () => {
  const app = buildApp();

  beforeAll(async () => {
    await app.ready();
  });

  afterAll(async () => {
    await app.close();
  });

  it('idempotent by requestId and stock decreases once', async () => {
    await fc.assert(
      fc.asyncProperty(reservationArb, async ({ requestId, sku, quantity, userId }) => {
        // reset state per run
        app.store.stock.clear();
        app.store.reservations.clear();
        const initialStock = Math.max(quantity + 1, 3);
        app.store.stock.set(sku, initialStock);

        const first = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: { requestId, sku, quantity, userId },
        });
        const second = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: { requestId, sku, quantity, userId },
        });

        expect(first.statusCode).toBe(200);
        expect(second.statusCode).toBe(200);
        expect(first.json()).toEqual(second.json());
        expect(app.store.stock.get(sku)).toBe(initialStock - quantity);
      }),
      { numRuns: defaultRuns },
    );
  });

  it('returns 409 when stock is insufficient and does not change stock', async () => {
    await fc.assert(
      fc.asyncProperty(insufficientArb, async ({ sku, stock, userId }) => {
        app.store.stock.clear();
        app.store.reservations.clear();
        app.store.stock.set(sku, stock);
        const quantity = stock + 1;

        const res = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: { requestId: 'req-' + stock, sku, quantity, userId },
        });

        expect(res.statusCode).toBe(409);
        expect(app.store.stock.get(sku)).toBe(stock);
      }),
      { numRuns: defaultRuns },
    );
  });
});
