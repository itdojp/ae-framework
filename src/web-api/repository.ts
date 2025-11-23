import { randomUUID } from 'node:crypto';

export type ReservationRecord = {
  reservationId: string;
  requestId: string;
  sku: string;
  quantity: number;
  status: 'reserved' | 'rejected';
};

export interface ReservationRepository {
  reset(stock: Record<string, number>): void;
  getStock(sku: string): number;
  upsertReservation(input: {
    requestId: string;
    sku: string;
    quantity: number;
  }): { record: ReservationRecord; updatedStock: number | null; conflict: boolean };
}

export class InMemoryReservationRepository implements ReservationRepository {
  private stock = new Map<string, number>();
  private reservations = new Map<string, ReservationRecord>();

  reset(stock: Record<string, number>): void {
    this.stock.clear();
    this.reservations.clear();
    for (const [sku, qty] of Object.entries(stock)) {
      this.stock.set(sku, qty);
    }
  }

  getStock(sku: string): number {
    return this.stock.get(sku) ?? 0;
  }

  upsertReservation(input: { requestId: string; sku: string; quantity: number }) {
    const { requestId, sku, quantity } = input;
    if (this.reservations.has(requestId)) {
      const record = this.reservations.get(requestId)!;
      return { record, updatedStock: null, conflict: false };
    }
    const current = this.stock.get(sku) ?? 0;
    if (current < quantity) {
      const record: ReservationRecord = {
        reservationId: '',
        requestId,
        sku,
        quantity,
        status: 'rejected',
      };
      return { record, updatedStock: null, conflict: true };
    }
    const nextStock = current - quantity;
    this.stock.set(sku, nextStock);
    const record: ReservationRecord = {
      reservationId: randomUUID(),
      requestId,
      sku,
      quantity,
      status: 'reserved',
    };
    this.reservations.set(requestId, record);
    return { record, updatedStock: nextStock, conflict: false };
  }
}
