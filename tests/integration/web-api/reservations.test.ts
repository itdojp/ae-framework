import { afterAll, beforeAll, describe, expect, it } from 'vitest';
import { buildApp, seedRepo } from '../../../src/web-api/app';
import { InMemoryReservationRepository } from '../../../src/web-api/repository';

const repo = new InMemoryReservationRepository();
const app = buildApp(repo);

// test:integration:webapi で実行

describe('web api / reservations', () => {
  beforeAll(async () => {
    await app.ready();
  });

  afterAll(async () => {
    await app.close();
  });

  it('creates a reservation when stock is sufficient', async () => {
    seedRepo(repo, { 'item-1': 5 });
    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { sku: 'item-1', quantity: 1, requestId: 'r1', userId: 'u1' },
    });
    expect(res.statusCode).toBe(200);
    expect(repo.getStock('item-1')).toBe(4);
  });

  it('is idempotent for the same requestId', async () => {
    seedRepo(repo, { 'item-1': 5 });
    const payload = { sku: 'item-1', quantity: 1, requestId: 'r2', userId: 'u1' };
    const first = await app.inject({ method: 'POST', url: '/reservations', payload });
    const second = await app.inject({ method: 'POST', url: '/reservations', payload });
    expect(first.statusCode).toBe(200);
    expect(second.statusCode).toBe(200);
    expect(first.json()).toEqual(second.json());
    expect(repo.getStock('item-1')).toBe(4);
  });

  it('returns 409 when stock is insufficient', async () => {
    seedRepo(repo, { 'item-1': 1 });
    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { sku: 'item-1', quantity: 10, requestId: 'r3', userId: 'u1' },
    });
    expect(res.statusCode).toBe(409);
    expect(repo.getStock('item-1')).toBe(1);
  });
});
