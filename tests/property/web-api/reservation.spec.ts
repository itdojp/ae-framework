import fc from 'fast-check';
import { beforeAll, afterAll, describe, it, expect } from 'vitest';
import { buildApp, seedRepo } from '../../../src/web-api/app';
import { InMemoryReservationRepository } from '../../../src/web-api/repository';
import { reservationArb, insufficientArb, defaultRuns } from './fast-check.config';

const repo = new InMemoryReservationRepository();
const app = buildApp(repo);

// property: idempotency and non-negative stock for reservations
// test:property:webapi で実行

describe('property: web api reservations', () => {
  beforeAll(async () => {
    await app.ready();
  });

  afterAll(async () => {
    await app.close();
  });

  it('idempotent by requestId and stock decreases once', async () => {
    await fc.assert(
      fc.asyncProperty(reservationArb, async ({ requestId, sku, quantity, userId }) => {
        const initialStock = Math.max(quantity + 1, 3);
        seedRepo(repo, { [sku]: initialStock });

        const payload = { requestId, sku, quantity, userId };
        const first = await app.inject({ method: 'POST', url: '/reservations', payload });
        const second = await app.inject({ method: 'POST', url: '/reservations', payload });

        expect(first.statusCode).toBe(200);
        expect(second.statusCode).toBe(200);
        expect(first.json()).toEqual(second.json());
        expect(repo.getStock(sku)).toBe(initialStock - quantity);
      }),
      { numRuns: defaultRuns },
    );
  });

  it('returns 409 when stock is insufficient and does not change stock', async () => {
    await fc.assert(
      fc.asyncProperty(insufficientArb, async ({ sku, stock, userId }) => {
        seedRepo(repo, { [sku]: stock });
        const quantity = stock + 1;

        const res = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: { requestId: 'req-' + stock, sku, quantity, userId },
        });

        expect(res.statusCode).toBe(409);
        expect(repo.getStock(sku)).toBe(stock);
      }),
      { numRuns: defaultRuns },
    );
  });
});
