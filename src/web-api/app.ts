import Fastify, { type FastifyInstance } from 'fastify';
import { randomUUID } from 'node:crypto';

export type ReservationRequest = {
  sku: string;
  quantity: number;
  requestId: string;
  userId?: string;
};

export type ReservationResponse = {
  reservationId: string;
  status: 'reserved' | 'rejected';
  error?: string;
};

type ValidationErrorResponse = { error: 'invalid_request'; details: string[] };
type ConflictResponse = { error: 'insufficient_stock'; reservationId: string; status: 'rejected'; remainingStock: number };

function createStore(initialStock: Record<string, number> = {}) {
  const stock = new Map<string, number>();
  const reservations = new Map<string, ReservationResponse>();
  for (const [sku, qty] of Object.entries(initialStock)) {
    stock.set(sku, qty);
  }
  return { stock, reservations };
}

declare module 'fastify' {
  interface FastifyInstance {
    store: ReturnType<typeof createStore>;
  }
}

export function buildApp(initialStock: Record<string, number> = {}): FastifyInstance {
  const app = Fastify({ logger: true });
  const store = createStore(initialStock);

  app.get('/health', async () => ({ status: 'ok' }));

  app.post<{
    Body: ReservationRequest;
    Reply: ReservationResponse | ValidationErrorResponse | ConflictResponse;
  }>(
    '/reservations',
    async (request, reply) => {
      const errors = validateRequest(request.body);
      if (errors.length > 0) {
        return reply.code(400).send({ error: 'invalid_request', details: errors });
      }
      const { sku, quantity, requestId } = request.body;
      if (store.reservations.has(requestId)) {
        return store.reservations.get(requestId)!;
      }
      const current = store.stock.get(sku) ?? 0;
      if (current < quantity) {
        return reply
          .code(409)
          .send({ error: 'insufficient_stock', reservationId: '', status: 'rejected', remainingStock: current });
      }
      store.stock.set(sku, current - quantity);
      const reservation = { reservationId: randomUUID(), status: 'reserved' } as const;
      store.reservations.set(requestId, reservation);
      return reservation;
    },
  );

  // exposed for tests and potential plugin usage
  app.decorate('store', store);
  return app;
}

export function seedStore(
  app: FastifyInstance & { store: ReturnType<typeof createStore> },
  entries: Record<string, number>,
) {
  app.store.stock.clear();
  app.store.reservations.clear();
  for (const [sku, stock] of Object.entries(entries)) {
    app.store.stock.set(sku, stock);
  }
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
