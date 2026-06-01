import { createHash, randomUUID } from 'node:crypto';

export type ReservationRecord = {
  reservationId: string;
  requestId: string;
  sku: string;
  quantity: number;
  status: 'reserved' | 'rejected';
};

export type IdempotencyConflict = {
  reason: 'principal_mismatch' | 'payload_mismatch';
  requestId: string;
};

export interface ReservationRepository {
  reset(stock: Record<string, number>): void;
  getStock(sku: string): number;
  /**
   * Idempotently create or fetch a reservation for the given requestId.
   *
   * Idempotency keys are bound to the authenticated principal and the canonical
   * reservation payload. Implementations must only return a duplicate record
   * when the same principal repeats the identical request payload.
   */
  upsertReservation(input: {
    principalId: string;
    requestId: string;
    sku: string;
    quantity: number;
  }): UpsertResult;
}

export type UpsertResult =
  | { kind: 'duplicate'; record: ReservationRecord; stock: number }
  | { kind: 'reserved'; record: ReservationRecord; stock: number }
  | { kind: 'rejected'; record: ReservationRecord; stock: number }
  | { kind: 'idempotency_conflict'; conflict: IdempotencyConflict };

type ReservationEntry = {
  principalId: string;
  payloadHash: string;
  record: ReservationRecord;
};

export class InMemoryReservationRepository implements ReservationRepository {
  private stock = new Map<string, number>();
  private reservations = new Map<string, ReservationEntry>();

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

  upsertReservation(input: { principalId: string; requestId: string; sku: string; quantity: number }): UpsertResult {
    const { principalId, requestId, sku, quantity } = input;
    const payloadHash = hashReservationPayload({ sku, quantity });
    const existing = this.reservations.get(requestId);
    if (existing) {
      if (existing.principalId !== principalId) {
        return { kind: 'idempotency_conflict', conflict: { reason: 'principal_mismatch', requestId } };
      }
      if (existing.payloadHash !== payloadHash) {
        return { kind: 'idempotency_conflict', conflict: { reason: 'payload_mismatch', requestId } };
      }
      return { kind: 'duplicate', record: existing.record, stock: this.stock.get(existing.record.sku) ?? 0 };
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
      this.reservations.set(requestId, { principalId, payloadHash, record });
      return { kind: 'rejected', record, stock: current };
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
    this.reservations.set(requestId, { principalId, payloadHash, record });
    return { kind: 'reserved', record, stock: nextStock };
  }
}

function hashReservationPayload(payload: { sku: string; quantity: number }): string {
  const canonicalPayload = JSON.stringify({ quantity: payload.quantity, sku: payload.sku });
  return createHash('sha256').update(canonicalPayload).digest('hex');
}
