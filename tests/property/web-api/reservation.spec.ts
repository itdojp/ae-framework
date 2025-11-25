import fc from 'fast-check';
import { describe, it, expect } from 'vitest';
import { buildApp, seedRepo } from '../../../src/web-api/app';
import { InMemoryReservationRepository } from '../../../src/web-api/repository';
import { reservationArb, insufficientArb, defaultRuns } from './fast-check.config';

// property: idempotency and non-negative stock for reservations
// test:property:webapi で実行

describe('property: web api reservations', () => {
  it('idempotent by requestId and stock decreases once', async () => {
    await fc.assert(
      fc.asyncProperty(reservationArb, async ({ requestId, sku, quantity, userId }) => {
        const repo = new InMemoryReservationRepository();
        const app = buildApp(repo);
        await app.ready();
        try {
          const initialStock = Math.max(quantity + 1, 3);
          seedRepo(repo, { [sku]: initialStock });

          const payload = { requestId, sku, quantity, userId };
          const first = await app.inject({ method: 'POST', url: '/reservations', payload });
          const second = await app.inject({ method: 'POST', url: '/reservations', payload });

          expect(first.statusCode).toBe(200);
          expect(second.statusCode).toBe(200);
          expect(first.json()).toEqual(second.json());
          expect(repo.getStock(sku)).toBe(initialStock - quantity);
        } finally {
          await app.close();
        }
      }),
      { numRuns: defaultRuns },
    );
  });

  it('returns 409 when stock is insufficient and does not change stock', async () => {
    await fc.assert(
      fc.asyncProperty(insufficientArb, async ({ requestId, sku, stock, userId }) => {
        const repo = new InMemoryReservationRepository();
        const app = buildApp(repo);
        await app.ready();
        try {
          seedRepo(repo, { [sku]: stock });
          const quantity = stock + 1;

          const res = await app.inject({
            method: 'POST',
            url: '/reservations',
            payload: { requestId, sku, quantity, userId },
          });

          expect(res.statusCode).toBe(409);
          expect(res.json()).toMatchObject({ error: 'insufficient_stock' });
          expect(repo.getStock(sku)).toBe(stock);
        } finally {
          await app.close();
        }
      }),
      { numRuns: defaultRuns },
    );
  });
});
