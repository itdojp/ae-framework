import { afterAll, beforeAll, describe, expect, it } from 'vitest';
import { buildApp, seedStore } from '../../../src/web-api/app';

// NOTE: test:fast では除外されるが、手動/CIでの動作確認用として有効化。
describe('web api / reservations', () => {
  const app = buildApp();

  beforeAll(async () => {
    await app.ready();
    seedStore(app, { 'item-1': 5 });
  });

  afterAll(async () => {
    await app.close();
  });

  it('creates a reservation when stock is sufficient', async () => {
    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { sku: 'item-1', quantity: 1, requestId: 'r1', userId: 'u1' },
    });
    expect(res.statusCode).toBe(200);
    expect(app.store.stock.get('item-1')).toBe(4);
  });

  it('is idempotent for the same requestId', async () => {
    const payload = { sku: 'item-1', quantity: 1, requestId: 'r2', userId: 'u1' };
    const first = await app.inject({ method: 'POST', url: '/reservations', payload });
    const second = await app.inject({ method: 'POST', url: '/reservations', payload });
    expect(first.statusCode).toBe(200);
    expect(second.statusCode).toBe(200);
    expect(first.json()).toEqual(second.json());
    expect(app.store.stock.get('item-1')).toBe(3);
  });

  it('returns 409 when stock is insufficient', async () => {
    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { sku: 'item-1', quantity: 10, requestId: 'r3', userId: 'u1' },
    });
    expect(res.statusCode).toBe(409);
  });
});
