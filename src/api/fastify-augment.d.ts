import 'fastify';
import type { Span } from '@opentelemetry/api';

declare module 'fastify' {
  interface FastifyRequest {
    span?: Span;
    startTime?: number;
  }
}

