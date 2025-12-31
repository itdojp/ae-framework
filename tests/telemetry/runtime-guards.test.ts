/**
 * Runtime Guards Tests
 * Tests for request/response validation and contract violation tracking
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { z } from 'zod';
import { RuntimeGuard, ViolationType, ViolationSeverity, CommonSchemas } from '../../src/telemetry/runtime-guards.js';

describe('Runtime Guards', () => {
  let guard: RuntimeGuard;

  beforeEach(() => {
    // Disable auto-initialization of telemetry for testing
    process.env.DISABLE_ENHANCED_TELEMETRY = 'true';
    guard = new RuntimeGuard();
  });

  afterEach(() => {
    delete process.env.DISABLE_ENHANCED_TELEMETRY;
  });

  describe('Request Validation', () => {
    const testSchema = z.object({
      name: z.string().min(1),
      age: z.number().int().positive(),
      email: z.string().email(),
    });

    it('should validate correct request data', () => {
      const validData = {
        name: 'John Doe',
        age: 30,
        email: 'john@example.com',
      };

      const result = guard.validateRequest(testSchema, validData, {
        requestId: 'test-req-123',
        endpoint: 'POST /users',
        operation: 'create_user',
      });

      expect(result.valid).toBe(true);
      expect(result.data).toEqual(validData);
      expect(result.violations).toHaveLength(0);
    });

    it('should reject invalid request data', () => {
      const invalidData = {
        name: '', // Invalid: empty string
        age: -5, // Invalid: negative number
        email: 'invalid-email', // Invalid: not an email
      };

      const result = guard.validateRequest(testSchema, invalidData, {
        requestId: 'test-req-456',
        endpoint: 'POST /users',
        operation: 'create_user',
      });

      expect(result.valid).toBe(false);
      expect(result.data).toBeUndefined();
      expect(result.violations).toHaveLength(1);
      
      const violation = result.violations[0];
      expect(violation.type).toBe(ViolationType.SCHEMA_VALIDATION);
      expect(violation.severity).toBe(ViolationSeverity.MEDIUM);
      expect(violation.requestId).toBe('test-req-456');
      expect(violation.endpoint).toBe('POST /users');
    });

    it('should handle missing required fields', () => {
      const incompleteData = {
        name: 'Jane Doe',
        // Missing age and email
      };

      const result = guard.validateRequest(testSchema, incompleteData, {
        requestId: 'test-req-789',
        endpoint: 'POST /users',
      });

      expect(result.valid).toBe(false);
      expect(result.violations).toHaveLength(1);
      
      const violation = result.violations[0];
      expect(violation.details?.issues).toBeDefined();
      expect(violation.details.issues.length).toBeGreaterThan(0);
    });
  });

  describe('Response Validation', () => {
    const responseSchema = z.object({
      id: z.string(),
      success: z.boolean(),
      timestamp: z.string(),
    });

    it('should validate correct response data', () => {
      const validResponse = {
        id: 'resp-123',
        success: true,
        timestamp: new Date().toISOString(),
      };

      const result = guard.validateResponse(responseSchema, validResponse, {
        requestId: 'test-req-123',
        endpoint: 'GET /status',
        statusCode: 200,
      });

      expect(result.valid).toBe(true);
      expect(result.data).toEqual(validResponse);
      expect(result.violations).toHaveLength(0);
    });

    it('should reject invalid response data with high severity', () => {
      const invalidResponse = {
        id: 123, // Invalid: should be string
        success: 'yes', // Invalid: should be boolean
        // Missing timestamp
      };

      const result = guard.validateResponse(responseSchema, invalidResponse, {
        requestId: 'test-req-456',
        endpoint: 'GET /status',
        statusCode: 200,
      });

      expect(result.valid).toBe(false);
      expect(result.violations).toHaveLength(1);
      
      const violation = result.violations[0];
      expect(violation.type).toBe(ViolationType.SCHEMA_VALIDATION);
      expect(violation.severity).toBe(ViolationSeverity.HIGH); // Response failures are high severity
      expect(violation.statusCode).toBeUndefined(); // statusCode not stored in violation
    });
  });

  describe('Business Rule Violations', () => {
    it('should record business rule violations', () => {
      const violation = guard.recordBusinessRuleViolation(
        'max_transfer_amount',
        'Transfer amount exceeds daily limit',
        ViolationSeverity.HIGH,
        { amount: 50000, limit: 10000, userId: 'user-123' }
      );

      expect(violation.type).toBe(ViolationType.BUSINESS_RULE);
      expect(violation.severity).toBe(ViolationSeverity.HIGH);
      expect(violation.message).toContain('Business rule violation: max_transfer_amount');
      expect(violation.details).toEqual({
        rule: 'max_transfer_amount',
        amount: 50000,
        limit: 10000,
        userId: 'user-123',
      });
    });
  });

  describe('Rate Limit Violations', () => {
    it('should record rate limit violations', () => {
      const violation = guard.recordRateLimitViolation(
        '/api/upload',
        100, // limit
        150, // current
        60000, // windowMs
        'req-rate-limit-test'
      );

      expect(violation.type).toBe(ViolationType.RATE_LIMIT);
      expect(violation.severity).toBe(ViolationSeverity.MEDIUM);
      expect(violation.message).toContain('Rate limit exceeded for /api/upload: 150/100 requests in 60000ms');
      expect(violation.endpoint).toBe('/api/upload');
      expect(violation.requestId).toBe('req-rate-limit-test');
      expect(violation.details).toEqual({
        limit: 100,
        current: 150,
        windowMs: 60000,
      });
    });
  });

  describe('Violation Statistics', () => {
    beforeEach(() => {
      // Add some test violations
      guard.recordBusinessRuleViolation('test_rule_1', 'Test violation 1', ViolationSeverity.LOW);
      guard.recordBusinessRuleViolation('test_rule_2', 'Test violation 2', ViolationSeverity.HIGH);
      guard.recordRateLimitViolation('/test', 10, 15, 60000);
    });

    it('should provide violation statistics', () => {
      const stats = guard.getViolationStats();

      expect(stats.total).toBeGreaterThanOrEqual(3);
      expect(stats.byType[ViolationType.BUSINESS_RULE]).toBeGreaterThanOrEqual(2);
      expect(stats.byType[ViolationType.RATE_LIMIT]).toBeGreaterThanOrEqual(1);
      expect(stats.bySeverity[ViolationSeverity.LOW]).toBeGreaterThanOrEqual(1);
      expect(stats.bySeverity[ViolationSeverity.HIGH]).toBeGreaterThanOrEqual(1);
      expect(stats.bySeverity[ViolationSeverity.MEDIUM]).toBeGreaterThanOrEqual(1);
      expect(stats.last24Hours).toBeGreaterThanOrEqual(3);
    });

    it('should get violations within time window', () => {
      const now = new Date();
      const oneHourAgo = new Date(now.getTime() - 60 * 60 * 1000);
      
      const recentViolations = guard.getViolations(oneHourAgo);
      
      expect(recentViolations.length).toBeGreaterThanOrEqual(3);
      recentViolations.forEach(violation => {
        expect(violation.timestamp.getTime()).toBeGreaterThanOrEqual(oneHourAgo.getTime());
      });
    });

    it('should clear old violations', () => {
      const initialCount = guard.getViolationStats().total;
      
      // Clear violations older than 1 hour from now (should clear none)
      const oneHourFromNow = new Date(Date.now() + 60 * 60 * 1000);
      const clearedCount = guard.clearOldViolations(oneHourFromNow);
      
      expect(clearedCount).toBe(initialCount);
      expect(guard.getViolationStats().total).toBe(0);
    });
  });

  describe('Common Schemas', () => {
    it('should validate health response schema', () => {
      const validHealthResponse = {
        status: 'healthy' as const,
        timestamp: new Date().toISOString(),
        service: 'test-service',
      };

      const result = CommonSchemas.HealthResponse.safeParse(validHealthResponse);
      expect(result.success).toBe(true);
    });

    it('should validate reservation request schema', () => {
      const validReservationRequest = {
        orderId: 'order-123',
        itemId: 'item-456',
        quantity: 5,
      };

      const result = CommonSchemas.ReservationRequest.safeParse(validReservationRequest);
      expect(result.success).toBe(true);
    });

    it('should reject invalid reservation request', () => {
      const invalidReservationRequest = {
        orderId: '', // Invalid: empty string
        itemId: 'item-456',
        quantity: -1, // Invalid: negative number
      };

      const result = CommonSchemas.ReservationRequest.safeParse(invalidReservationRequest);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error.issues.length).toBeGreaterThan(0);
      }
    });

    it('should validate reservation response schema', () => {
      const validReservationResponse = {
        ok: true,
        reservationId: 'res-123',
      };

      const result = CommonSchemas.ReservationResponse.safeParse(validReservationResponse);
      expect(result.success).toBe(true);
    });

    it('should validate error response schema', () => {
      const validErrorResponse = {
        error: 'VALIDATION_ERROR',
        message: 'Request validation failed',
        details: { field: 'quantity', issue: 'must be positive' },
      };

      const result = CommonSchemas.ErrorResponse.safeParse(validErrorResponse);
      expect(result.success).toBe(true);
    });
  });
});
