import Fastify, { FastifyInstance } from 'fastify';
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
};

function createStore() {
  const stock = new Map<string, number>();
  const reservations = new Map<string, ReservationResponse>();
  return { stock, reservations };
}

export function buildApp(): FastifyInstance {
  const app = Fastify({ logger: false });
  const store = createStore();

  app.get('/health', async () => ({ status: 'ok' }));

  app.post<{ Body: ReservationRequest; Reply: ReservationResponse }>(
    '/reservations',
    async (request, reply) => {
      const { sku, quantity, requestId } = request.body;
      if (!sku || !quantity || quantity < 1) {
        return reply.code(400).send({ reservationId: '', status: 'rejected' });
      }
      if (store.reservations.has(requestId)) {
        return store.reservations.get(requestId)!;
      }
      const current = store.stock.get(sku) ?? 0;
      if (current < quantity) {
        return reply.code(409).send({ reservationId: '', status: 'rejected' });
      }
      store.stock.set(sku, current - quantity);
      const reservation = { reservationId: randomUUID(), status: 'reserved' } as const;
      store.reservations.set(requestId, reservation);
      return reservation;
    },
  );

  app.decorate('store', store);
  return app;
}
