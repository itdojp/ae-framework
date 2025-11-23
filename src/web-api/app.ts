import Fastify, { type FastifyInstance } from 'fastify';
import { InMemoryReservationRepository, type ReservationRepository, type ReservationRecord } from './repository.js';

export type ReservationRequest = {
  sku: string;
  quantity: number;
  requestId: string;
  userId?: string;
};

type ValidationErrorResponse = { error: 'invalid_request'; details: string[] };
type ConflictResponse = { error: 'insufficient_stock'; record: ReservationRecord; remainingStock: number };

function createRepo(): ReservationRepository {
  return new InMemoryReservationRepository();
}

declare module 'fastify' {
  interface FastifyInstance {
    repo: ReservationRepository;
  }
}

export function buildApp(repo: ReservationRepository = createRepo()): FastifyInstance {
  const app = Fastify({ logger: false });

  app.get('/health', async () => ({ status: 'ok' }));

  app.post<{ Body: ReservationRequest; Reply: ReservationRecord | ValidationErrorResponse | ConflictResponse }>(
    '/reservations',
    async (request, reply) => {
      const validationErrors = validateRequest(request.body);
      if (validationErrors.length > 0) {
        return reply.code(400).send({ error: 'invalid_request', details: validationErrors });
      }

      const result = repo.upsertReservation({
        requestId: request.body.requestId,
        sku: request.body.sku,
        quantity: request.body.quantity,
      });

      if (result.record.status === 'rejected') {
        return reply
          .code(409)
          .send({ error: 'insufficient_stock', record: result.record, remainingStock: result.stock });
      }

      return reply.send(result.record);
    },
  );

  app.decorate('repo', repo);
  return app;
}

export function seedRepo(repo: ReservationRepository, entries: Record<string, number>) {
  repo.reset(entries);
}

function validateRequest(body: ReservationRequest): string[] {
  const errors: string[] = [];
  if (!body.requestId || typeof body.requestId !== 'string') {
    errors.push('requestId is required');
  }
  if (!body.sku || typeof body.sku !== 'string') {
    errors.push('sku is required');
  }
  if (body.quantity === undefined || typeof body.quantity !== 'number' || Number.isNaN(body.quantity)) {
    errors.push('quantity must be a number');
  } else if (!Number.isInteger(body.quantity) || body.quantity < 1) {
    errors.push('quantity must be an integer >= 1');
  }
  return errors;
}
