import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import type { SpyInstance } from 'vitest';
import { FastifyInstance } from 'fastify';
import { trace } from '@opentelemetry/api';
import { formatGWT } from '../utils/gwt-format';
import * as SecurityHeaders from '../../src/api/middleware/security-headers.js';
import getServer, { createServer } from '../../src/api/server.js';

const {
  timerEndSpy,
  createTimerSpy,
  recordQualityMetricsSpy,
  recordCounterSpy,
  runtimeGuardMocks,
} = vi.hoisted(() => {
  const timerEnd = vi.fn();
  const createTimer = vi.fn(() => ({ end: timerEnd }));

  return {
    timerEndSpy: timerEnd,
    createTimerSpy: createTimer,
    recordQualityMetricsSpy: vi.fn(),
    recordCounterSpy: vi.fn(),
    runtimeGuardMocks: {
      validateRequest: vi.fn(),
      validateResponse: vi.fn(),
      recordBusinessRuleViolation: vi.fn(),
      getViolationStats: vi.fn(),
    },
  };
});

vi.mock('../../src/telemetry/enhanced-telemetry.js', () => ({
  enhancedTelemetry: {
    createTimer: createTimerSpy,
    recordQualityMetrics: recordQualityMetricsSpy,
    recordCounter: recordCounterSpy,
  },
  TELEMETRY_ATTRIBUTES: {
    REQUEST_ID: 'telemetry.request_id',
    SERVICE_COMPONENT: 'telemetry.service_component',
    SERVICE_OPERATION: 'telemetry.service_operation',
    DURATION_MS: 'telemetry.duration_ms',
  },
}));

vi.mock('../../src/telemetry/runtime-guards.js', () => ({
  runtimeGuard: runtimeGuardMocks,
  CommonSchemas: {
    ReservationRequest: {},
    ReservationResponse: {},
    HealthResponse: {},
  },
  ViolationSeverity: {
    MEDIUM: 'medium',
  },
}));

let consoleErrorSpy: ReturnType<typeof vi.spyOn<typeof console, 'error'>>;

const setupDefaultTelemetryMocks = () => {
  consoleErrorSpy?.mockRestore();
  vi.clearAllMocks();
  timerEndSpy.mockReset();
  createTimerSpy.mockImplementation(() => ({ end: timerEndSpy }));

  runtimeGuardMocks.validateRequest.mockImplementation(() => ({
    valid: true,
    data: {
      orderId: 'order-1',
      itemId: 'item-1',
      quantity: 1,
    },
  }));

  runtimeGuardMocks.validateResponse.mockImplementation(() => ({
    valid: true,
    violations: [],
  }));

  runtimeGuardMocks.recordBusinessRuleViolation.mockImplementation(() => {});
  runtimeGuardMocks.getViolationStats.mockImplementation(() => ({
    total: 0,
  }));

  consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
};

describe('Reservations API telemetry integration', () => {
  beforeEach(() => {
    setupDefaultTelemetryMocks();
  });

  afterEach(() => {
    consoleErrorSpy?.mockRestore();
  });

  it(
    formatGWT(
      'POST /reservations (valid payload)',
      'completes successfully',
      'timer/quality metrics are recorded with success flags',
    ),
    async () => {
      const app: FastifyInstance = await createServer();
      app.addHook('preHandler', (request, _reply, done) => {
        // @ts-expect-error span is cleared to simulate missing instrumentation
        delete request.span;
        done();
      });
      await app.ready();

      try {
        const response = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: {
            orderId: 'order-1',
            itemId: 'item-1',
            quantity: 1,
          },
        });

        expect(response.statusCode).toBe(201);
        const payload = JSON.parse(response.body);
        expect(payload).toEqual({ ok: true });
        expect(createTimerSpy).toHaveBeenCalledWith('api.reservations.duration');
        expect(runtimeGuardMocks.validateRequest).toHaveBeenCalledWith(
          {},
          expect.anything(),
          expect.objectContaining({
            endpoint: 'POST /reservations',
            operation: 'create_reservation',
            requestId: expect.any(String),
          }),
        );
        expect(runtimeGuardMocks.validateResponse).toHaveBeenCalledWith(
          {},
          expect.objectContaining({ ok: true }),
          expect.objectContaining({
            endpoint: 'POST /reservations',
            statusCode: 201,
            requestId: expect.any(String),
          }),
        );
        expect(recordQualityMetricsSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            component: 'reservations',
            phase: 'runtime',
            score: 100,
          }),
        );
        expect(timerEndSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            endpoint: '/reservations',
            result: 'success',
            validation_result: 'success',
          }),
        );
        expect(runtimeGuardMocks.recordBusinessRuleViolation).not.toHaveBeenCalled();
        expect(consoleErrorSpy).not.toHaveBeenCalled();
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'POST /reservations (quantity over 100)',
      'triggers business rule guard',
      'business rule violation is recorded and success metrics are not emitted',
    ),
    async () => {
      runtimeGuardMocks.validateRequest.mockImplementation(() => ({
        valid: true,
        data: {
          orderId: 'order-2',
          itemId: 'item-2',
          quantity: 150,
        },
      }));

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: {
            orderId: 'order-2',
            itemId: 'item-2',
            quantity: 150,
          },
        });

        expect(response.statusCode).toBe(400);
        const payload = JSON.parse(response.body);
        expect(payload).toEqual({
          error: 'BUSINESS_RULE_VIOLATION',
          message: 'Quantity exceeds maximum allowed limit of 100',
        });
        expect(recordQualityMetricsSpy).not.toHaveBeenCalled();
        expect(runtimeGuardMocks.recordBusinessRuleViolation).toHaveBeenCalledWith(
          'max_quantity_limit',
          expect.stringContaining('Quantity 150 exceeds'),
          'medium',
          expect.objectContaining({
            orderId: 'order-2',
            itemId: 'item-2',
            quantity: 150,
          }),
        );
        expect(timerEndSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            endpoint: '/reservations',
            result: 'business_rule_violation',
          }),
        );
        expect(runtimeGuardMocks.validateResponse).not.toHaveBeenCalled();
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'POST /reservations (quantity at limit)',
      'allows upper bound value',
      'business rule guard remains idle when quantity is 100',
    ),
    async () => {
      runtimeGuardMocks.validateRequest.mockImplementation(() => ({
        valid: true,
        data: {
          orderId: 'order-100',
          itemId: 'item-100',
          quantity: 100,
        },
      }));

      const app: FastifyInstance = await createServer();
      app.addHook('preHandler', (request, _reply, done) => {
        // @ts-expect-error span is cleared to simulate missing instrumentation
        delete request.span;
        done();
      });
      await app.ready();

      try {
        const response = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: {
            orderId: 'order-100',
            itemId: 'item-100',
            quantity: 100,
          },
        });

        expect(response.statusCode).toBe(201);
        expect(runtimeGuardMocks.recordBusinessRuleViolation).not.toHaveBeenCalled();
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'POST /reservations (invalid payload)',
      'is rejected by runtime guard validation',
      'violations are returned and telemetry marks validation_error',
    ),
    async () => {
      runtimeGuardMocks.validateRequest.mockImplementation(() => ({
        valid: false,
        violations: undefined,
      }));

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: {},
        });

        expect(response.statusCode).toBe(400);
        const body = JSON.parse(response.body);
        expect(body).toEqual({
          error: 'VALIDATION_ERROR',
          message: 'Request payload validation failed',
          details: 'Validation failed',
          violation_id: 'unknown',
        });
        expect(timerEndSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            endpoint: '/reservations',
            result: 'validation_error',
            violation_type: 'unknown',
          }),
        );
        expect(recordQualityMetricsSpy).not.toHaveBeenCalled();
        expect(runtimeGuardMocks.recordBusinessRuleViolation).not.toHaveBeenCalled();
        expect(runtimeGuardMocks.validateResponse).not.toHaveBeenCalled();
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'POST /reservations (response validation failure)',
      'keeps responding but flags quality metrics',
      'response validation failure is logged and scored as 0',
    ),
    async () => {
      runtimeGuardMocks.validateResponse.mockImplementation(() => ({
        valid: false,
        violations: [
          {
            id: 'reservation.response.shape',
            type: 'schema',
            details: 'ok flag missing',
          },
        ],
      }));

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: {
            orderId: 'order-3',
            itemId: 'item-3',
            quantity: 5,
          },
        });

        expect(response.statusCode).toBe(201);
        expect(timerEndSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            endpoint: '/reservations',
            result: 'success',
            validation_result: 'failure',
          }),
        );
        expect(recordQualityMetricsSpy).toHaveBeenCalledWith(
          expect.objectContaining({ score: 0 }),
        );
        expect(consoleErrorSpy).toHaveBeenCalledWith(
          'Reservation response validation failed:',
          expect.arrayContaining([
            expect.objectContaining({ id: 'reservation.response.shape' }),
          ]),
        );
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'POST /reservations (unexpected exception)',
      'throws inside handler',
      'timer and span record exceptions before bubbling up',
    ),
    async () => {
      runtimeGuardMocks.validateResponse.mockImplementation(() => {
        throw new Error('response failure');
      });

      const spanSpy = vi.fn();
      const app: FastifyInstance = await createServer();
      app.addHook('preHandler', (request, _reply, done) => {
        const span: any = request.span;
        if (span) {
          const originalRecord = span.recordException?.bind(span);
          span.recordException = vi.fn((error: Error) => {
            spanSpy(error);
            return originalRecord?.(error);
          });
        }
        done();
      });
      await app.ready();

      try {
        const response = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: {
            orderId: 'order-err',
            itemId: 'item-err',
            quantity: 2,
          },
        });

        expect(response.statusCode).toBe(500);
        const errorBody = JSON.parse(response.body);
        expect(errorBody.message).toContain('response failure');
        expect(timerEndSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            endpoint: '/reservations',
            result: 'error',
          }),
        );
        expect(spanSpy).toHaveBeenCalledWith(expect.any(Error));
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'POST /reservations (unexpected exception without span)',
      'throws before span is attached',
      'timer still records error without crashing on missing span',
    ),
    async () => {
      runtimeGuardMocks.validateRequest.mockImplementation(() => ({
        valid: true,
        data: {
          orderId: 'order-missing-span',
          itemId: 'item-missing-span',
          quantity: 10,
        },
      }));

      runtimeGuardMocks.validateResponse.mockImplementation(() => {
        throw new Error('response failure');
      });

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({
          method: 'POST',
          url: '/reservations',
          payload: {
            orderId: 'order-missing-span',
            itemId: 'item-missing-span',
            quantity: 10,
          },
        });

        expect(response.statusCode).toBe(500);
        const errorBody = JSON.parse(response.body);
        expect(errorBody.message).toContain('response failure');
        expect(timerEndSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            endpoint: '/reservations',
            result: 'error',
          }),
        );
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'GET /api/runtime-guard/stats',
      'returns runtime guard metrics',
      'payload includes aggregated violation stats',
    ),
    async () => {
      const mockStats = {
        data_validation: 2,
        business_rules: 1,
      };
      runtimeGuardMocks.getViolationStats.mockReturnValue(mockStats);

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/api/runtime-guard/stats',
        });

        expect(response.statusCode).toBe(200);
        const payload = JSON.parse(response.body);
        expect(payload.violations).toEqual(mockStats);
        expect(payload.timestamp).toBeDefined();
        expect(payload.uptime).toBeGreaterThanOrEqual(0);
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'GET /api/runtime-guard/stats (runtime failure)',
      'throws while collecting stats',
      'span records exception before error propagates',
    ),
    async () => {
      runtimeGuardMocks.getViolationStats.mockImplementation(() => {
        throw new Error('stats failed');
      });

      const app: FastifyInstance = await createServer();
      const spanSpy = vi.fn();
      app.addHook('preHandler', (request, _reply, done) => {
        const span: any = request.span;
        if (span) {
          const originalRecord = span.recordException?.bind(span);
          span.recordException = vi.fn((error: Error) => {
            spanSpy(error);
            return originalRecord?.(error);
          });
        }
        done();
      });
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/api/runtime-guard/stats',
        });

        expect(response.statusCode).toBe(500);
        expect(spanSpy).toHaveBeenCalledWith(expect.any(Error));
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'GET /api/runtime-guard/stats (runtime failure without span)',
      'throws but no span is present',
      'error response is emitted without attempting to record span',
    ),
    async () => {
      runtimeGuardMocks.getViolationStats.mockImplementation(() => {
        throw new Error('stats failed');
      });

      const app: FastifyInstance = await createServer();
      app.addHook('preHandler', (request, _reply, done) => {
        // @ts-expect-error span is cleared to simulate missing instrumentation
        delete request.span;
        done();
      });
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/api/runtime-guard/stats',
        });

        expect(response.statusCode).toBe(500);
        const payload = JSON.parse(response.body);
        expect(payload.message).toContain('stats failed');
      } finally {
        await app.close();
      }
    },
  );
});

describe('Health endpoint telemetry integration', () => {
  beforeEach(() => {
    setupDefaultTelemetryMocks();
  });

  afterEach(() => {
    consoleErrorSpy?.mockRestore();
  });

  it(
    formatGWT(
      'GET /health (valid response)',
      'returns healthy payload',
      'telemetry records success metrics',
    ),
    async () => {
      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/health',
        });

        expect(response.statusCode).toBe(200);
        const payload = JSON.parse(response.body);
        expect(payload.status).toBe('healthy');
        expect(payload.service).toBe('ae-framework-api');
        expect(createTimerSpy).toHaveBeenCalledWith('api.health_check.duration');
        expect(runtimeGuardMocks.validateResponse).toHaveBeenCalledWith(
          {},
          expect.objectContaining({ status: 'healthy' }),
          expect.objectContaining({
            endpoint: 'GET /health',
            statusCode: 200,
            requestId: expect.any(String),
          }),
        );
        expect(timerEndSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            endpoint: '/health',
            validation_result: 'success',
          }),
        );
        expect(recordQualityMetricsSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            component: 'health-check',
            phase: 'runtime',
            score: 100,
          }),
        );
        expect(consoleErrorSpy).not.toHaveBeenCalled();
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'GET /health (response validation failure)',
      'still returns payload',
      'logs validation error and drops quality score',
    ),
    async () => {
      runtimeGuardMocks.validateResponse.mockImplementationOnce(() => ({
        valid: false,
        violations: [
          { id: 'health.schema', type: 'schema', details: 'invalid payload' },
        ],
      }));

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/health',
        });

        expect(response.statusCode).toBe(200);
        expect(consoleErrorSpy).toHaveBeenCalledWith(
          'Health check response validation failed:',
          expect.arrayContaining([
            expect.objectContaining({ id: 'health.schema' }),
          ]),
        );
        expect(timerEndSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            endpoint: '/health',
            validation_result: 'failure',
          }),
        );
        expect(recordQualityMetricsSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            component: 'health-check',
            score: 0,
          }),
        );
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'GET /health (unexpected exception)',
      'throws during validation',
      'timer and span capture health failure',
    ),
    async () => {
      runtimeGuardMocks.validateResponse.mockImplementationOnce(() => {
        throw new Error('health failure');
      });

      const spanSpy = vi.fn();
      const app: FastifyInstance = await createServer();
      app.addHook('preHandler', (request, _reply, done) => {
        const span: any = request.span;
        if (span) {
          const originalRecord = span.recordException?.bind(span);
          span.recordException = vi.fn((error: Error) => {
            spanSpy(error);
            return originalRecord?.(error);
          });
        }
        done();
      });
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/health',
        });

        expect(response.statusCode).toBe(500);
        const payload = JSON.parse(response.body);
        expect(payload.message).toContain('health failure');
        expect(timerEndSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            endpoint: '/health',
            result: 'error',
          }),
        );
        expect(spanSpy).toHaveBeenCalledWith(expect.any(Error));
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'GET /health (unexpected exception without span)',
      'throws without instrumentation',
      'error propagates while timer captures failure',
    ),
    async () => {
      runtimeGuardMocks.validateResponse.mockImplementationOnce(() => {
        throw new Error('health failure');
      });

      const app: FastifyInstance = await createServer();
      app.addHook('preHandler', (request, _reply, done) => {
        // @ts-expect-error span is cleared to simulate missing instrumentation
        delete request.span;
        done();
      });
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/health',
        });

        expect(response.statusCode).toBe(500);
        const payload = JSON.parse(response.body);
        expect(payload.message).toContain('health failure');
        expect(timerEndSpy).toHaveBeenCalledWith(
          expect.objectContaining({
            endpoint: '/health',
            result: 'error',
          }),
        );
      } finally {
        await app.close();
      }
    },
  );
});

describe('getServer default export', () => {
  it('returns a configured Fastify instance', async () => {
    const server = await getServer();
    expect(server).toBeTruthy();
    expect(typeof server.inject).toBe('function');
    expect(typeof server.close).toBe('function');
    await server.close();
  });
});
