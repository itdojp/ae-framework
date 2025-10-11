import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import type { SpyInstance } from 'vitest';
import { FastifyInstance } from 'fastify';
import { trace } from '@opentelemetry/api';
import { formatGWT } from '../utils/gwt-format';
import * as SecurityHeaders from '../../src/api/middleware/security-headers.js';
import { TELEMETRY_ATTRIBUTES } from '../../src/telemetry/enhanced-telemetry.js';
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

const setupDefaultTelemetryMocks = () => {
  vi.clearAllMocks();
  timerEndSpy.mockReset();
  createTimerSpy.mockImplementation(() => ({ end: timerEndSpy }));
  recordQualityMetricsSpy.mockReset();
  recordCounterSpy.mockReset();
  runtimeGuardMocks.validateRequest.mockReset();
  runtimeGuardMocks.validateResponse.mockReset();
  runtimeGuardMocks.recordBusinessRuleViolation.mockReset();
  runtimeGuardMocks.getViolationStats.mockReset();

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

  const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
  return consoleErrorSpy;
};

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

describe('Server instrumentation telemetry', () => {
  let consoleErrorSpy: ReturnType<typeof vi.spyOn<typeof console, 'error'>>;
  let tracerSpy: SpyInstance | undefined;

  beforeEach(() => {
    consoleErrorSpy = setupDefaultTelemetryMocks();
    tracerSpy = undefined;
  });

  afterEach(() => {
    tracerSpy?.mockRestore();
    consoleErrorSpy?.mockRestore();
  });

  it(
    formatGWT(
      'createServer',
      'generates prefixed request ids',
      'Fastify genReqId emits req_<timestamp>_<random> format',
    ),
    async () => {
      const app: FastifyInstance = await createServer();

      try {
        expect((app as any).log.level).toBe('info');

        const firstId = (app as any).genReqId();
        const secondId = (app as any).genReqId();

        expect(firstId).toMatch(/^req_\d{13}_[a-z0-9]{9}$/);
        expect(secondId).toMatch(/^req_\d{13}_[a-z0-9]{9}$/);
        expect(secondId).not.toBe(firstId);
      } finally {
        await app.close();
      }
    },
  );

  it(
    formatGWT(
      'request tracing',
      'handles successful response',
      'records tracing attributes and counters',
    ),
    async () => {
      const spanStub = {
        setAttributes: vi.fn(),
        recordException: vi.fn(),
        end: vi.fn(),
      };
      const startSpan = vi.fn(() => spanStub);
      tracerSpy = vi.spyOn(trace, 'getTracer').mockReturnValue({ startSpan } as any);

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/health',
        });

        expect(response.statusCode).toBe(200);
        expect(tracerSpy).toHaveBeenCalledWith('ae-framework-api');
        expect(startSpan).toHaveBeenCalledWith(
          'GET /health',
          expect.objectContaining({
            attributes: expect.objectContaining({
              [TELEMETRY_ATTRIBUTES.REQUEST_ID]: expect.any(String),
              [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'api-server',
              [TELEMETRY_ATTRIBUTES.SERVICE_OPERATION]: 'GET /health',
              'http.method': 'GET',
              'http.url': '/health',
              'http.user_agent': 'lightMyRequest',
            }),
          }),
        );

        const attributes = spanStub.setAttributes.mock.calls[0][0];
        expect(attributes).toEqual(
          expect.objectContaining({
            'http.status_code': 200,
            [TELEMETRY_ATTRIBUTES.DURATION_MS]: expect.any(Number),
          }),
        );
        const duration = attributes[TELEMETRY_ATTRIBUTES.DURATION_MS] as number;
        expect(duration).toBeGreaterThanOrEqual(0);
        expect(duration).toBeLessThan(10000);

        expect(spanStub.recordException).not.toHaveBeenCalled();
        expect(spanStub.end).toHaveBeenCalled();

        expect(recordCounterSpy).toHaveBeenCalledWith(
          'api.requests.total',
          1,
          expect.objectContaining({
            method: 'GET',
            endpoint: '/health',
          }),
        );

        expect(recordCounterSpy).toHaveBeenCalledWith(
          'api.responses.total',
          1,
          expect.objectContaining({
            method: 'GET',
            endpoint: '/health',
            status_code: '200',
          }),
        );
      } finally {
        await app.close();
        tracerSpy?.mockRestore();
        tracerSpy = undefined;
      }
    },
  );

  it(
    formatGWT(
      'request tracing',
      'handles missing user agent',
      'applies unknown fallback in span attributes',
    ),
    async () => {
      const spanStub = {
        setAttributes: vi.fn(),
        recordException: vi.fn(),
        end: vi.fn(),
      };
      const startSpan = vi.fn(() => spanStub);
      tracerSpy = vi.spyOn(trace, 'getTracer').mockReturnValue({ startSpan } as any);

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/health',
          headers: { 'user-agent': '' },
        });

        expect(response.statusCode).toBe(200);
        expect(startSpan).toHaveBeenCalledWith(
          'GET /health',
          expect.objectContaining({
            attributes: expect.objectContaining({
              'http.user_agent': 'unknown',
            }),
          }),
        );
      } finally {
        await app.close();
        tracerSpy?.mockRestore();
        tracerSpy = undefined;
      }
    },
  );

  it(
    formatGWT(
      'request tracing',
      'captures error response',
      'records exception metadata and error counters',
    ),
    async () => {
      const spanStub = {
        setAttributes: vi.fn(),
        recordException: vi.fn(),
        end: vi.fn(),
      };
      const startSpan = vi.fn(() => spanStub);
      tracerSpy = vi.spyOn(trace, 'getTracer').mockReturnValue({ startSpan } as any);

      runtimeGuardMocks.validateResponse.mockImplementationOnce(() => {
        throw new Error('response failure');
      });

      const app: FastifyInstance = await createServer();
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
        expect(spanStub.recordException).toHaveBeenCalledWith(
          expect.objectContaining({ message: 'HTTP 500' }),
        );
        expect(recordCounterSpy).toHaveBeenCalledWith(
          'api.responses.total',
          1,
          expect.objectContaining({
            method: 'POST',
            endpoint: '/reservations',
            status_code: '500',
          }),
        );
      } finally {
        await app.close();
        tracerSpy?.mockRestore();
        tracerSpy = undefined;
      }
    },
  );

  it(
    formatGWT(
      'request tracing',
      'captures validation failure',
      'flags 400 responses as exceptions',
    ),
    async () => {
      const spanStub = {
        setAttributes: vi.fn(),
        recordException: vi.fn(),
        end: vi.fn(),
      };
      const startSpan = vi.fn(() => spanStub);
      tracerSpy = vi.spyOn(trace, 'getTracer').mockReturnValue({ startSpan } as any);

      runtimeGuardMocks.validateRequest.mockImplementationOnce(() => ({
        valid: false,
        violations: [
          { id: 'reservation.quantity.min', type: 'schema', details: 'quantity must be >= 1' },
        ],
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
        expect(spanStub.recordException).toHaveBeenCalledWith(
          expect.objectContaining({ message: 'HTTP 400' }),
        );
        expect(recordCounterSpy).toHaveBeenCalledWith(
          'api.responses.total',
          1,
          expect.objectContaining({
            method: 'POST',
            endpoint: '/reservations',
            status_code: '400',
          }),
        );
      } finally {
        await app.close();
        tracerSpy?.mockRestore();
        tracerSpy = undefined;
      }
    },
  );

  it(
    formatGWT(
      'security headers (test)',
      'returns hardened defaults',
      'enforces CSP and strips server signatures in test mode',
    ),
    async () => {
      const originalEnv = process.env.NODE_ENV;
      process.env.NODE_ENV = 'test';
      const getConfigSpy = vi.spyOn(SecurityHeaders, 'getSecurityConfiguration');

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({ method: 'GET', url: '/health' });
        expect(response.statusCode).toBe(200);
        expect(response.headers['content-security-policy']).toBe("default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self'; test-mode 'enabled';");
        expect(response.headers['permissions-policy']).toContain('test-mode=()');
        expect(response.headers['x-frame-options']).toBe('DENY');
        expect(response.headers['server']).toBeUndefined();
        expect(response.headers['x-powered-by']).toBeUndefined();
        expect(getConfigSpy).not.toHaveBeenCalled();
      } finally {
        await app.close();
        getConfigSpy.mockRestore();
        process.env.NODE_ENV = originalEnv;
      }
    },
  );

  it(
    formatGWT(
      'security headers (non-test)',
      'uses environment configuration',
      'defers to getSecurityConfiguration when not in test mode',
    ),
    async () => {
      const originalEnv = process.env.NODE_ENV;
      process.env.NODE_ENV = 'production';
      const getConfigSpy = vi
        .spyOn(SecurityHeaders, 'getSecurityConfiguration')
        .mockReturnValue({ enabled: false });

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({ method: 'GET', url: '/health' });
        expect(response.statusCode).toBe(200);
        expect(response.headers['x-frame-options']).toBeUndefined();
        expect(getConfigSpy).toHaveBeenCalled();
      } finally {
        await app.close();
        getConfigSpy.mockRestore();
        process.env.NODE_ENV = originalEnv;
      }
    },
  );

  it(
    formatGWT(
      'request tracing',
      'handles missing user agent',
      'applies unknown fallback in span attributes',
    ),
    async () => {
      const spanStub = {
        setAttributes: vi.fn(),
        recordException: vi.fn(),
        end: vi.fn(),
      };
      const startSpan = vi.fn(() => spanStub);
      tracerSpy = vi.spyOn(trace, 'getTracer').mockReturnValue({ startSpan } as any);

      const app: FastifyInstance = await createServer();
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/health',
          headers: { 'user-agent': '' },
        });

        expect(response.statusCode).toBe(200);
        expect(startSpan).toHaveBeenCalledWith(
          'GET /health',
          expect.objectContaining({
            attributes: expect.objectContaining({
              'http.user_agent': 'unknown',
            }),
          }),
        );
      } finally {
        await app.close();
        tracerSpy?.mockRestore();
        tracerSpy = undefined;
      }
    },
  );

  it(
    formatGWT(
      'request tracing',
      'handles missing span',
      'completes responses when trace span is absent',
    ),
    async () => {
      const app: FastifyInstance = await createServer();
      app.addHook('preHandler', (request, _reply, done) => {
        // @ts-expect-error simulate missing instrumentation
        delete request.span;
        done();
      });
      await app.ready();

      try {
        const response = await app.inject({
          method: 'GET',
          url: '/health',
        });
        expect(response.statusCode).toBe(200);
        expect(recordCounterSpy).toHaveBeenCalledWith(
          'api.responses.total',
          1,
          expect.objectContaining({
            method: 'GET',
            endpoint: '/health',
            status_code: '200',
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
