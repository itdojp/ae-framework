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
export declare class InsufficientStockError extends Error {
    constructor(itemId: string, requested: number, available: number);
}
