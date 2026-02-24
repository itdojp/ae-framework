import Fastify from 'fastify';
import { afterEach, describe, expect, it, vi } from 'vitest';

import { reservationRoutes } from '../../src/api/routes/reservations.js';
import { IdempotencyConflictError, InsufficientStockError } from '../../src/domain/entities.js';
import type { InventoryService } from '../../src/domain/services.js';

function createInventoryService(overrides: Partial<InventoryService> = {}): InventoryService {
  const defaults: InventoryService = {
    checkAvailability: vi.fn().mockResolvedValue(true),
    createReservation: vi.fn().mockResolvedValue({
      id: 'res-1',
      orderId: 'order-1',
      itemId: 'item-1',
      quantity: 1,
      createdAt: new Date('2026-01-01T00:00:00.000Z'),
      status: 'confirmed',
    }),
    getItem: vi.fn().mockResolvedValue(null),
  };

  return {
    ...defaults,
    ...overrides,
  };
}

const apps: Array<ReturnType<typeof Fastify>> = [];

afterEach(async () => {
  while (apps.length > 0) {
    const app = apps.pop();
    if (app) {
      await app.close();
    }
  }
});

async function buildApp(inventoryService: InventoryService) {
  const app = Fastify();
  apps.push(app);
  await app.register(reservationRoutes, { inventoryService });
  await app.ready();
  return app;
}

describe('reservationRoutes', () => {
  it('returns 409 when createReservation throws InsufficientStockError', async () => {
    const inventoryService = createInventoryService({
      createReservation: vi.fn().mockRejectedValue(
        new InsufficientStockError('item-1', 10, 0),
      ),
    });
    const app = await buildApp(inventoryService);

    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { orderId: 'order-1', itemId: 'item-1', quantity: 10 },
    });

    expect(res.statusCode).toBe(409);
    expect(res.json()).toMatchObject({
      error: 'INSUFFICIENT_STOCK',
      message: expect.stringContaining('Insufficient stock'),
    });
  });

  it('returns 500 when createReservation throws unexpected error', async () => {
    const inventoryService = createInventoryService({
      createReservation: vi.fn().mockRejectedValue(new Error('Unexpected failure')),
    });
    const app = await buildApp(inventoryService);

    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { orderId: 'order-1', itemId: 'item-1', quantity: 1 },
    });

    expect(res.statusCode).toBe(500);
    const body = res.json();
    expect(body).toHaveProperty('error');
    expect(body).toHaveProperty('message');
    expect(typeof body.error).toBe('string');
    expect(typeof body.message).toBe('string');
  });

  it('returns 409 when createReservation throws IdempotencyConflictError', async () => {
    const inventoryService = createInventoryService({
      createReservation: vi.fn().mockRejectedValue(
        new IdempotencyConflictError('order-1', 'item-1', 2),
      ),
    });
    const app = await buildApp(inventoryService);

    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { orderId: 'order-1', itemId: 'item-1', quantity: 2 },
    });

    expect(res.statusCode).toBe(409);
    expect(res.json()).toMatchObject({
      error: 'IDEMPOTENCY_CONFLICT',
      message: expect.stringContaining('Idempotency conflict'),
    });
  });
});
