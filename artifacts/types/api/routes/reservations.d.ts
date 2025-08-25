import { FastifyInstance } from 'fastify';
import { InventoryService } from '../../domain/services.js';
export declare function reservationRoutes(fastify: FastifyInstance, options: {
    inventoryService: InventoryService;
}): Promise<void>;
