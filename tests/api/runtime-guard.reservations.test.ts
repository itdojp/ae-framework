import { describe, it, expect, vi, beforeEach } from 'vitest';
import { FastifyInstance } from 'fastify';
import { formatGWT } from '../utils/gwt-format';

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

import { createServer } from '../../src/api/server.js';

describe('Reservations API telemetry integration', () => {
  beforeEach(() => {
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
  });

  it(
    formatGWT(
      'POST /reservations (valid payload)',
      'completes successfully',
      'timer/quality metrics are recorded with success flags',
    ),
    async () => {
      const app: FastifyInstance = await createServer();
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
});
