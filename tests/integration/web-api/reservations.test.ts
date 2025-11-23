import { afterAll, beforeAll, describe, expect, it } from 'vitest';
import { buildApp } from '../../../src/web-api/app';

// NOTE: スケルトン。CIの test:fast では実行されない。必要に応じて skip を外して拡張してください。
describe.skip('web api / reservations', () => {
  const app = buildApp();

  beforeAll(async () => {
    await app.ready();
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
  });
});
