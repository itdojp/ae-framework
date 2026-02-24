import type { FastifyInstance } from 'fastify';
import { Reservation } from '../../domain/contracts.js';
import type { InventoryService } from '../../domain/services.js';
import { normalizeError } from '../../resilience/error-utils.js';

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
    } catch (error: unknown) {
      const normalizedError = normalizeError(error, 'Reservation creation failed');
      if (normalizedError.name === 'InsufficientStockError') {
        return reply.code(409).send({
          error: 'INSUFFICIENT_STOCK',
          message: normalizedError.message,
          details: parsed.data,
        });
      }
      if (normalizedError.name === 'IdempotencyConflictError') {
        return reply.code(409).send({
          error: 'IDEMPOTENCY_CONFLICT',
          message: normalizedError.message,
          details: parsed.data,
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
