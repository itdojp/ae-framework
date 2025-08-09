export interface Item {
  id: string;
  name: string;
  stock: number;
  reserved: number;
}

export interface ReservationEntity {
  id: string;
  orderId: string;
  itemId: string;
  quantity: number;
  createdAt: Date;
  status: 'pending' | 'confirmed' | 'cancelled';
}

export class InsufficientStockError extends Error {
  constructor(itemId: string, requested: number, available: number) {
    super(`Insufficient stock for item ${itemId}: requested ${requested}, available ${available}`);
    this.name = 'InsufficientStockError';
  }
}