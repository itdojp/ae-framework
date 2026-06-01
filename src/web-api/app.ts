import Fastify, { type FastifyInstance, type FastifyRequest } from 'fastify';
import { InMemoryReservationRepository, type ReservationRepository, type ReservationRecord } from './repository.js';

export type ReservationRequest = {
  sku: string;
  quantity: number;
  requestId: string;
  userId?: string;
};

type ReservationRouteRequest = FastifyRequest<{ Body: ReservationRequest }>;

export type ReservationPrincipalResolver = (request: ReservationRouteRequest) => Promise<string | undefined> | string | undefined;

export type BuildAppOptions = {
  /**
   * Resolves the authenticated principal for a reservation request.
   * Integrations should provide this from an auth middleware or trusted upstream
   * context. The request body userId is never used as authority.
   */
  resolvePrincipal?: ReservationPrincipalResolver;
};

type ValidationErrorResponse = { error: 'invalid_request'; details: string[] };
type AuthenticationErrorResponse = { error: 'unauthorized'; details: string[] };
type AuthorizationErrorResponse = { error: 'forbidden'; details: string[] };
type ConflictResponse = { error: 'insufficient_stock'; record: ReservationRecord; remainingStock: number };
type IdempotencyConflictResponse = {
  error: 'idempotency_conflict';
  details: string[];
  reason: 'principal_mismatch' | 'payload_mismatch';
};

function createRepo(): ReservationRepository {
  return new InMemoryReservationRepository();
}

declare module 'fastify' {
  interface FastifyInstance {
    repo: ReservationRepository;
  }
}

export function buildApp(repo: ReservationRepository = createRepo(), options: BuildAppOptions = {}): FastifyInstance {
  const app = Fastify({ logger: false });
  const resolvePrincipal = options.resolvePrincipal ?? rejectUnauthenticatedPrincipal;

  app.get('/health', async () => ({ status: 'ok' }));

  app.post<{
    Body: ReservationRequest;
    Reply:
      | ReservationRecord
      | ValidationErrorResponse
      | AuthenticationErrorResponse
      | AuthorizationErrorResponse
      | ConflictResponse
      | IdempotencyConflictResponse;
  }>('/reservations', async (request, reply) => {
    const validationErrors = validateRequest(request.body);
    if (validationErrors.length > 0) {
      return reply.code(400).send({ error: 'invalid_request', details: validationErrors });
    }

    const principalId = normalizePrincipalId(await resolvePrincipal(request));
    if (!principalId) {
      return reply.code(401).send({ error: 'unauthorized', details: ['authenticated principal is required'] });
    }
    if (request.body.userId !== undefined && request.body.userId !== principalId) {
      return reply.code(403).send({
        error: 'forbidden',
        details: ['body userId must match the authenticated principal'],
      });
    }

    const result = repo.upsertReservation({
      principalId,
      requestId: request.body.requestId,
      sku: request.body.sku,
      quantity: request.body.quantity,
    });

    if (result.kind === 'idempotency_conflict') {
      return reply.code(409).send({
        error: 'idempotency_conflict',
        reason: result.conflict.reason,
        details: ['idempotency key already exists for a different principal or payload'],
      });
    }

    if (result.record.status === 'rejected') {
      return reply
        .code(409)
        .send({ error: 'insufficient_stock', record: result.record, remainingStock: result.stock });
    }

    return reply.send(result.record);
  });

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
  if (body.userId !== undefined && typeof body.userId !== 'string') {
    errors.push('userId must be a string when provided');
  }
  return errors;
}

function rejectUnauthenticatedPrincipal(): undefined {
  return undefined;
}

export function resolvePrincipalFromHeaders(request: ReservationRouteRequest): string | undefined {
  return normalizeHeaderPrincipal(request.headers['x-principal-id']) ?? normalizeHeaderPrincipal(request.headers['x-user-id']);
}

function normalizeHeaderPrincipal(headerValue: string | string[] | undefined): string | undefined {
  if (Array.isArray(headerValue)) {
    if (headerValue.length !== 1) {
      return undefined;
    }
    return normalizePrincipalId(headerValue[0]);
  }
  return normalizePrincipalId(headerValue);
}

function normalizePrincipalId(value: string | undefined): string | undefined {
  const normalized = value?.trim();
  return normalized && normalized.length > 0 ? normalized : undefined;
}
