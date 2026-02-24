import type { FastifyInstance } from 'fastify';
import { afterEach, describe, expect, it } from 'vitest';

import { createServer } from '../../src/api/server.js';
import { InMemoryInventoryRepository, InventoryServiceImpl } from '../../src/domain/services.js';

const apps: FastifyInstance[] = [];

const createApp = async (
  seedItems: Array<{ id: string; name: string; stock: number; reserved: number }>,
) => {
  const repository = new InMemoryInventoryRepository(seedItems);
  const inventoryService = new InventoryServiceImpl(repository);
  const app = await createServer({ inventoryService });
  apps.push(app);
  await app.ready();
  return app;
};

afterEach(async () => {
  while (apps.length > 0) {
    const app = apps.pop();
    if (app) {
      await app.close();
    }
  }
});

describe('POST /reservations integration', () => {
  it('returns reservationId on success', async () => {
    const app = await createApp([{ id: 'item-1', name: 'Item 1', stock: 10, reserved: 0 }]);

    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { orderId: 'order-1', itemId: 'item-1', quantity: 3 },
    });

    expect(res.statusCode).toBe(201);
    expect(res.json()).toMatchObject({
      ok: true,
      reservationId: expect.any(String),
    });
  });

  it('returns 409 when stock is insufficient', async () => {
    const app = await createApp([{ id: 'item-1', name: 'Item 1', stock: 1, reserved: 1 }]);

    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { orderId: 'order-1', itemId: 'item-1', quantity: 1 },
    });

    expect(res.statusCode).toBe(409);
    expect(res.json()).toMatchObject({
      error: 'INSUFFICIENT_STOCK',
      message: expect.stringContaining('Insufficient stock'),
    });
  });

  it('returns same reservationId for idempotent replay', async () => {
    const app = await createApp([{ id: 'item-1', name: 'Item 1', stock: 10, reserved: 0 }]);

    const first = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { orderId: 'order-1', itemId: 'item-1', quantity: 2 },
    });
    const second = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { orderId: 'order-1', itemId: 'item-1', quantity: 2 },
    });
    const firstBody = first.json() as { ok: boolean; reservationId: string };
    const secondBody = second.json() as { ok: boolean; reservationId: string };

    expect(first.statusCode).toBe(201);
    expect(second.statusCode).toBe(201);
    expect(secondBody).toMatchObject({
      ok: true,
      reservationId: firstBody.reservationId,
    });
  });

  it('returns 409 when same orderId is reused with a different payload', async () => {
    const app = await createApp([{ id: 'item-1', name: 'Item 1', stock: 10, reserved: 0 }]);

    await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { orderId: 'order-1', itemId: 'item-1', quantity: 2 },
    });

    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { orderId: 'order-1', itemId: 'item-1', quantity: 3 },
    });

    expect(res.statusCode).toBe(409);
    expect(res.json()).toMatchObject({
      error: 'IDEMPOTENCY_CONFLICT',
      message: expect.stringContaining('Idempotency conflict'),
    });
  });
});
