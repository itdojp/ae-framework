import { Item, ReservationEntity } from './entities.js';
import { Reservation } from './contracts.js';
export interface InventoryService {
    checkAvailability(itemId: string, quantity: number): Promise<boolean>;
    createReservation(reservation: Reservation): Promise<ReservationEntity>;
    getItem(itemId: string): Promise<Item | null>;
}
export declare class InventoryServiceImpl implements InventoryService {
    private _db;
    constructor(_db: any);
    checkAvailability(itemId: string, quantity: number): Promise<boolean>;
    createReservation(reservation: Reservation): Promise<ReservationEntity>;
    getItem(_itemId: string): Promise<Item | null>;
}
