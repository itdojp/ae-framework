import { describe, expect, it, vi } from 'vitest';

import { IdempotencyConflictError, InsufficientStockError } from '../../src/domain/entities.js';
import {
  DatabaseInventoryRepository,
  InMemoryInventoryRepository,
  InventoryServiceImpl,
} from '../../src/domain/services.js';

describe('InventoryServiceImpl', () => {
  it('creates reservation and updates reserved count within a transaction', async () => {
    const txExecutor = {
      query: vi
        .fn()
        .mockResolvedValueOnce({ rows: [] })
        .mockResolvedValueOnce({
          rows: [{ id: 'item-1', name: 'Item 1', stock: 10, reserved: 2 }],
        })
        .mockResolvedValueOnce({
          rows: [
            {
              id: 'res-1',
              order_id: 'order-1',
              item_id: 'item-1',
              quantity: 3,
              status: 'confirmed',
              created_at: '2026-02-24T00:00:00.000Z',
            },
          ],
        })
        .mockResolvedValueOnce({ rows: [] }),
    };

    const db = {
      query: vi.fn(),
      transaction: vi.fn(async (callback: (executor: typeof txExecutor) => Promise<unknown>) =>
        callback(txExecutor),
      ),
    };

    const repository = new DatabaseInventoryRepository(db);
    const service = new InventoryServiceImpl(repository);

    const result = await service.createReservation({
      orderId: 'order-1',
      itemId: 'item-1',
      quantity: 3,
    });

    expect(db.transaction).toHaveBeenCalledTimes(1);
    expect(txExecutor.query).toHaveBeenCalledWith(
      expect.stringContaining('FROM reservations'),
      ['order-1'],
    );
    expect(txExecutor.query).toHaveBeenCalledWith(
      expect.stringContaining('FOR UPDATE'),
      ['item-1'],
    );
    expect(txExecutor.query).toHaveBeenCalledWith(
      expect.stringContaining('INSERT INTO reservations'),
      expect.arrayContaining(['order-1', 'item-1', 3]),
    );
    expect(txExecutor.query).toHaveBeenCalledWith(
      expect.stringContaining('SET reserved = reserved + $1'),
      [3, 'item-1'],
    );
    expect(result).toMatchObject({
      id: 'res-1',
      orderId: 'order-1',
      itemId: 'item-1',
      quantity: 3,
      status: 'confirmed',
    });
  });

  it('returns existing reservation for idempotent replay', async () => {
    const repository = new InMemoryInventoryRepository([
      { id: 'item-1', name: 'Item 1', stock: 10, reserved: 0 },
    ]);
    const service = new InventoryServiceImpl(repository);

    const first = await service.createReservation({
      orderId: 'order-1',
      itemId: 'item-1',
      quantity: 2,
    });
    const second = await service.createReservation({
      orderId: 'order-1',
      itemId: 'item-1',
      quantity: 2,
    });
    const item = await service.getItem('item-1');

    expect(second.id).toBe(first.id);
    expect(item?.reserved).toBe(2);
  });

  it('throws IdempotencyConflictError when duplicate orderId has different payload', async () => {
    const repository = new InMemoryInventoryRepository([
      { id: 'item-1', name: 'Item 1', stock: 10, reserved: 0 },
    ]);
    const service = new InventoryServiceImpl(repository);

    await service.createReservation({
      orderId: 'order-1',
      itemId: 'item-1',
      quantity: 2,
    });

    await expect(
      service.createReservation({
        orderId: 'order-1',
        itemId: 'item-1',
        quantity: 3,
      }),
    ).rejects.toBeInstanceOf(IdempotencyConflictError);
  });

  it('throws InsufficientStockError when stock is not enough', async () => {
    const repository = new InMemoryInventoryRepository([
      { id: 'item-1', name: 'Item 1', stock: 1, reserved: 1 },
    ]);
    const service = new InventoryServiceImpl(repository);

    await expect(
      service.createReservation({
        orderId: 'order-1',
        itemId: 'item-1',
        quantity: 1,
      }),
    ).rejects.toBeInstanceOf(InsufficientStockError);
  });

  it('auto provisions unknown items when in-memory repository option is enabled', async () => {
    const repository = new InMemoryInventoryRepository([], [], {
      autoProvisionUnknownItems: true,
      defaultStock: 5,
    });
    const service = new InventoryServiceImpl(repository);

    const available = await service.checkAvailability('item-new', 4);
    const unavailable = await service.checkAvailability('item-new', 6);
    const item = await service.getItem('item-new');

    expect(available).toBe(true);
    expect(unavailable).toBe(false);
    expect(item).toMatchObject({
      id: 'item-new',
      stock: 5,
      reserved: 0,
    });
  });
});
