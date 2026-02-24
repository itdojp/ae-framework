import { randomUUID } from 'crypto';

import { IdempotencyConflictError, InsufficientStockError } from './entities.js';
import type { Item, ReservationEntity } from './entities.js';
import type { Reservation } from './contracts.js';

type QueryResult<Row> = {
  rows: Row[];
};

type QueryExecutor = {
  query<Row extends Record<string, unknown>>(
    text: string,
    params?: ReadonlyArray<unknown>,
  ): Promise<QueryResult<Row>>;
};

type TransactionExecutor = QueryExecutor & {
  transaction<T>(callback: (executor: QueryExecutor) => Promise<T>): Promise<T>;
};

type ReservationRow = {
  id: string;
  order_id: string;
  item_id: string;
  quantity: number;
  status: ReservationEntity['status'];
  created_at: string | Date;
};

type ItemRow = {
  id: string;
  name: string;
  stock: number;
  reserved: number;
};

const toDate = (value: string | Date): Date => (value instanceof Date ? value : new Date(value));

const toReservationEntity = (row: ReservationRow): ReservationEntity => ({
  id: row.id,
  orderId: row.order_id,
  itemId: row.item_id,
  quantity: Number(row.quantity),
  createdAt: toDate(row.created_at),
  status: row.status,
});

const toItem = (row: ItemRow): Item => ({
  id: row.id,
  name: row.name,
  stock: Number(row.stock),
  reserved: Number(row.reserved),
});

export interface InventoryRepository {
  withTransaction<T>(callback: (repository: InventoryRepository) => Promise<T>): Promise<T>;
  findItemById(itemId: string, options?: { forUpdate?: boolean }): Promise<Item | null>;
  findReservationByOrderId(orderId: string): Promise<ReservationEntity | null>;
  createReservation(input: Reservation): Promise<ReservationEntity>;
  incrementReservedCount(itemId: string, quantity: number): Promise<void>;
}

export class DatabaseInventoryRepository implements InventoryRepository {
  private readonly queryExecutor: QueryExecutor;

  constructor(
    private readonly db: TransactionExecutor,
    queryExecutor?: QueryExecutor,
  ) {
    this.queryExecutor = queryExecutor ?? db;
  }

  async withTransaction<T>(callback: (repository: InventoryRepository) => Promise<T>): Promise<T> {
    return this.db.transaction(async (executor) => {
      const transactionalRepository = new DatabaseInventoryRepository(this.db, executor);
      return callback(transactionalRepository);
    });
  }

  async findItemById(itemId: string, options?: { forUpdate?: boolean }): Promise<Item | null> {
    const lockClause = options?.forUpdate ? ' FOR UPDATE' : '';
    const result = await this.queryExecutor.query<ItemRow>(
      `SELECT id, name, stock, reserved FROM items WHERE id = $1${lockClause}`,
      [itemId],
    );

    const row = result.rows[0];
    return row ? toItem(row) : null;
  }

  async findReservationByOrderId(orderId: string): Promise<ReservationEntity | null> {
    const result = await this.queryExecutor.query<ReservationRow>(
      `
        SELECT id, order_id, item_id, quantity, status, created_at
        FROM reservations
        WHERE order_id = $1
      `,
      [orderId],
    );

    const row = result.rows[0];
    return row ? toReservationEntity(row) : null;
  }

  async createReservation(input: Reservation): Promise<ReservationEntity> {
    const reservationId = randomUUID();
    const result = await this.queryExecutor.query<ReservationRow>(
      `
        INSERT INTO reservations (id, order_id, item_id, quantity, status)
        VALUES ($1, $2, $3, $4, 'confirmed')
        RETURNING id, order_id, item_id, quantity, status, created_at
      `,
      [reservationId, input.orderId, input.itemId, input.quantity],
    );

    return toReservationEntity(result.rows[0]);
  }

  async incrementReservedCount(itemId: string, quantity: number): Promise<void> {
    await this.queryExecutor.query(
      `
        UPDATE items
        SET reserved = reserved + $1,
            updated_at = CURRENT_TIMESTAMP
        WHERE id = $2
      `,
      [quantity, itemId],
    );
  }
}

export interface InMemoryInventoryRepositoryOptions {
  autoProvisionUnknownItems?: boolean;
  defaultStock?: number;
}

export class InMemoryInventoryRepository implements InventoryRepository {
  private readonly items = new Map<string, Item>();
  private readonly reservationsByOrderId = new Map<string, ReservationEntity>();
  private readonly autoProvisionUnknownItems: boolean;
  private readonly defaultStock: number;

  constructor(
    seedItems: Item[] = [],
    seedReservations: ReservationEntity[] = [],
    options: InMemoryInventoryRepositoryOptions = {},
  ) {
    this.autoProvisionUnknownItems = options.autoProvisionUnknownItems ?? false;
    this.defaultStock = options.defaultStock ?? 1000;

    seedItems.forEach((item) => {
      this.items.set(item.id, { ...item });
    });
    seedReservations.forEach((reservation) => {
      this.reservationsByOrderId.set(reservation.orderId, { ...reservation });
    });
  }

  async withTransaction<T>(callback: (repository: InventoryRepository) => Promise<T>): Promise<T> {
    return callback(this);
  }

  findItemById(itemId: string): Promise<Item | null> {
    const existing = this.items.get(itemId);
    if (existing) {
      return Promise.resolve({ ...existing });
    }

    if (!this.autoProvisionUnknownItems) {
      return Promise.resolve(null);
    }

    const provisioned: Item = {
      id: itemId,
      name: `Item ${itemId}`,
      stock: this.defaultStock,
      reserved: 0,
    };
    this.items.set(itemId, provisioned);
    return Promise.resolve({ ...provisioned });
  }

  findReservationByOrderId(orderId: string): Promise<ReservationEntity | null> {
    const existing = this.reservationsByOrderId.get(orderId);
    return Promise.resolve(existing ? { ...existing } : null);
  }

  createReservation(input: Reservation): Promise<ReservationEntity> {
    const created: ReservationEntity = {
      id: randomUUID(),
      orderId: input.orderId,
      itemId: input.itemId,
      quantity: input.quantity,
      createdAt: new Date(),
      status: 'confirmed',
    };
    this.reservationsByOrderId.set(created.orderId, created);
    return Promise.resolve({ ...created });
  }

  incrementReservedCount(itemId: string, quantity: number): Promise<void> {
    const item = this.items.get(itemId);
    if (!item) {
      return Promise.resolve();
    }

    this.items.set(itemId, {
      ...item,
      reserved: item.reserved + quantity,
    });
    return Promise.resolve();
  }
}

export interface InventoryService {
  checkAvailability(itemId: string, quantity: number): Promise<boolean>;
  createReservation(reservation: Reservation): Promise<ReservationEntity>;
  getItem(itemId: string): Promise<Item | null>;
}

export class InventoryServiceImpl implements InventoryService {
  constructor(private readonly repository: InventoryRepository) {}

  async checkAvailability(itemId: string, quantity: number): Promise<boolean> {
    const item = await this.repository.findItemById(itemId);
    if (!item) {
      return false;
    }

    return item.stock - item.reserved >= quantity;
  }

  async createReservation(reservation: Reservation): Promise<ReservationEntity> {
    return this.repository.withTransaction(async (repository) => {
      const existing = await repository.findReservationByOrderId(reservation.orderId);
      if (existing) {
        if (existing.itemId !== reservation.itemId || existing.quantity !== reservation.quantity) {
          throw new IdempotencyConflictError(
            reservation.orderId,
            reservation.itemId,
            reservation.quantity,
          );
        }
        return existing;
      }

      const item = await repository.findItemById(reservation.itemId, { forUpdate: true });
      const available = item ? item.stock - item.reserved : 0;
      if (available < reservation.quantity) {
        throw new InsufficientStockError(reservation.itemId, reservation.quantity, available);
      }

      const createdReservation = await repository.createReservation(reservation);
      await repository.incrementReservedCount(reservation.itemId, reservation.quantity);
      return createdReservation;
    });
  }

  async getItem(itemId: string): Promise<Item | null> {
    return this.repository.findItemById(itemId);
  }
}
