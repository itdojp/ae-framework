import { Item, ReservationEntity, InsufficientStockError } from './entities.js';
import { Reservation } from './contracts.js';

export interface InventoryService {
  checkAvailability(itemId: string, quantity: number): Promise<boolean>;
  createReservation(reservation: Reservation): Promise<ReservationEntity>;
  getItem(itemId: string): Promise<Item | null>;
}

export class InventoryServiceImpl implements InventoryService {
  constructor(private db: any) {}

  async checkAvailability(itemId: string, quantity: number): Promise<boolean> {
    const item = await this.getItem(itemId);
    if (!item) return false;
    return (item.stock - item.reserved) >= quantity;
  }

  async createReservation(reservation: Reservation): Promise<ReservationEntity> {
    const available = await this.checkAvailability(reservation.itemId, reservation.quantity);
    if (!available) {
      const item = await this.getItem(reservation.itemId);
      throw new InsufficientStockError(
        reservation.itemId,
        reservation.quantity,
        item ? item.stock - item.reserved : 0
      );
    }

    // TODO: Implement idempotency check for orderId
    // TODO: Create reservation in database with transaction
    // TODO: Update item reserved count

    return {
      id: 'generated-id',
      ...reservation,
      createdAt: new Date(),
      status: 'confirmed'
    };
  }

  async getItem(itemId: string): Promise<Item | null> {
    // TODO: Implement database query
    return null;
  }
}