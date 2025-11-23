import Fastify, { FastifyInstance } from 'fastify';
import { InMemoryReservationRepository, ReservationRepository, ReservationRecord } from './repository';

export type ReservationRequest = {
  sku: string;
  quantity: number;
  requestId: string;
  userId?: string;
};

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

  app.post<{ Body: ReservationRequest; Reply: ReservationRecord }>(
    '/reservations',
    async (request, reply) => {
      const { sku, quantity, requestId } = request.body;
      if (!sku || !quantity || quantity < 1) {
        return reply.code(400).send({ reservationId: '', requestId, sku, quantity, status: 'rejected' });
      }
      const result = repo.upsertReservation({ requestId, sku, quantity });
      if (result.conflict) {
        return reply.code(409).send(result.record);
      }
      return result.record;
    },
  );

  app.decorate('repo', repo);
  return app;
}

export function seedRepo(repo: ReservationRepository, entries: Record<string, number>) {
  repo.reset(entries);
}
