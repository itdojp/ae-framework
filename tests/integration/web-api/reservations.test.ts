import { describe, expect, it } from 'vitest';
import { buildApp, seedRepo } from '../../../src/web-api/app';
import { InMemoryReservationRepository } from '../../../src/web-api/repository';
import { applyIntegrationRetry } from '../../_helpers/integration-test-utils.js';

// test:integration:webapi で実行

applyIntegrationRetry(it);

async function buildTestApp() {
  const repo = new InMemoryReservationRepository();
  const app = buildApp(repo);
  await app.ready();
  return { repo, app };
}

describe('web api / reservations', () => {
  it('creates a reservation when stock is sufficient', async () => {
    const { repo, app } = await buildTestApp();
    try {
      seedRepo(repo, { 'item-1': 5 });
      const res = await app.inject({
        method: 'POST',
        url: '/reservations',
        payload: { sku: 'item-1', quantity: 1, requestId: 'r1', userId: 'u1' },
      });
      expect(res.statusCode).toBe(200);
      expect(repo.getStock('item-1')).toBe(4);
    } finally {
      await app.close();
    }
  });

  it('is idempotent for the same requestId', async () => {
    const { repo, app } = await buildTestApp();
    try {
      seedRepo(repo, { 'item-1': 5 });
      const payload = { sku: 'item-1', quantity: 1, requestId: 'r2', userId: 'u1' };
      const first = await app.inject({ method: 'POST', url: '/reservations', payload });
      const second = await app.inject({ method: 'POST', url: '/reservations', payload });
      expect(first.statusCode).toBe(200);
      expect(second.statusCode).toBe(200);
      expect(first.json()).toEqual(second.json());
      expect(repo.getStock('item-1')).toBe(4);
    } finally {
      await app.close();
    }
  });

  it('returns 409 when stock is insufficient and caches rejection', async () => {
    const { repo, app } = await buildTestApp();
    try {
      seedRepo(repo, { 'item-1': 1 });
      const payload = { sku: 'item-1', quantity: 10, requestId: 'r3', userId: 'u1' };
      const first = await app.inject({ method: 'POST', url: '/reservations', payload });
      const second = await app.inject({ method: 'POST', url: '/reservations', payload });
      expect(first.statusCode).toBe(409);
      expect(second.statusCode).toBe(409);
      expect(first.json()).toEqual(second.json());
      expect(repo.getStock('item-1')).toBe(1);
    } finally {
      await app.close();
    }
  });

  it('returns 400 when requestId is missing', async () => {
    const { repo, app } = await buildTestApp();
    try {
      seedRepo(repo, { 'item-1': 5 });
      const res = await app.inject({
        method: 'POST',
        url: '/reservations',
        payload: { sku: 'item-1', quantity: 1, userId: 'u1' },
      });
      expect(res.statusCode).toBe(400);
      expect(res.json()).toMatchObject({ error: 'invalid_request' });
    } finally {
      await app.close();
    }
  });
});
