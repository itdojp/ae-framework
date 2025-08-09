import { FastifyInstance } from 'fastify';
import { Reservation } from '../../domain/contracts';
import { InventoryService } from '../../domain/services';

export async function reservationRoutes(fastify: FastifyInstance, options: { inventoryService: InventoryService }) {
  const { inventoryService } = options;

  fastify.post('/reservations', async (request, reply) => {
    const parsed = Reservation.safeParse(request.body);
    
    if (!parsed.success) {
      return reply.code(400).send({
        error: 'VALIDATION_ERROR',
        details: parsed.error.errors
      });
    }

    try {
      const reservation = await inventoryService.createReservation(parsed.data);
      return reply.code(201).send(reservation);
    } catch (error: any) {
      if (error.name === 'InsufficientStockError') {
        return reply.code(409).send({
          error: 'INSUFFICIENT_STOCK',
          message: error.message
        });
      }
      throw error;
    }
  });

  fastify.get('/items/:itemId/availability', async (request, reply) => {
    const { itemId } = request.params as { itemId: string };
    const { quantity } = request.query as { quantity?: string };
    
    if (!quantity || isNaN(Number(quantity))) {
      return reply.code(400).send({
        error: 'VALIDATION_ERROR',
        message: 'Quantity parameter is required and must be a number'
      });
    }

    const available = await inventoryService.checkAvailability(itemId, Number(quantity));
    return reply.send({ itemId, quantity: Number(quantity), available });
  });
}