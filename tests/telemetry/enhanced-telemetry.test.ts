/**
 * Enhanced OpenTelemetry Implementation Tests
 * Tests for Observable Gauges and standardized metrics
 */

import { describe, it, expect, beforeAll, afterAll, vi } from 'vitest';
import { EnhancedTelemetry, TELEMETRY_ATTRIBUTES } from '../../src/telemetry/enhanced-telemetry.js';

describe('Enhanced OpenTelemetry', () => {
  let telemetry: EnhancedTelemetry;

  beforeAll(() => {
    // Disable auto-initialization for testing
    process.env.DISABLE_ENHANCED_TELEMETRY = 'true';
    telemetry = new EnhancedTelemetry({
      serviceName: 'test-service',
      serviceVersion: '1.0.0-test',
      environment: 'test',
      enableMetrics: true,
      enableTracing: false, // Disable tracing for simpler testing
      enableLogging: false,
    });
  });

  afterAll(async () => {
    await telemetry.shutdown();
    delete process.env.DISABLE_ENHANCED_TELEMETRY;
  });

  it('should initialize with correct configuration', () => {
    expect(telemetry).toBeInstanceOf(EnhancedTelemetry);
  });

  it('should provide standardized attribute names', () => {
    expect(TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT).toBe('service.component');
    expect(TELEMETRY_ATTRIBUTES.REQUEST_ID).toBe('request.id');
    expect(TELEMETRY_ATTRIBUTES.ERROR_TYPE).toBe('error.type');
    expect(TELEMETRY_ATTRIBUTES.DURATION_MS).toBe('duration.ms');
  });

  it('should record counters with attributes', () => {
    const spy = vi.spyOn(console, 'log').mockImplementation(() => {});
    
    telemetry.recordCounter('test.counter', 5, {
      [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'test-component',
      test_attribute: 'test_value',
    });

    // Counter recording doesn't throw - that's the main test
    expect(() => {
      telemetry.recordCounter('test.counter.2', 1);
    }).not.toThrow();

    spy.mockRestore();
  });

  it('should record gauge values with attributes', () => {
    expect(() => {
      telemetry.recordGauge('test.gauge', 42, {
        [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'test-component',
      });
    }).not.toThrow();
  });

  it('should create and use timer', async () => {
    const timer = telemetry.createTimer('test.operation', {
      [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'timer-test',
    });

    // Simulate some work
    await new Promise(resolve => setTimeout(resolve, 10));

    const duration = timer.end({
      result: 'success',
    });

    expect(duration).toBeGreaterThan(0);
    expect(duration).toBeLessThan(1000); // Should be less than 1 second
  });

  it('should record contract violations', () => {
    expect(() => {
      telemetry.recordContractViolation(
        'schema_validation',
        'test-contract-123',
        'high',
        {
          endpoint: '/test',
          error_details: 'Invalid payload',
        }
      );
    }).not.toThrow();
  });

  it('should record quality metrics', () => {
    expect(() => {
      telemetry.recordQualityMetrics({
        coverage: 85.5,
        score: 92.0,
        phase: 'test-phase',
        component: 'test-component',
      });
    }).not.toThrow();
  });

  it('should handle initialization gracefully', () => {
    const testTelemetry = new EnhancedTelemetry({
      serviceName: 'test-init',
      enableMetrics: false,
      enableTracing: false,
    });

    expect(() => {
      testTelemetry.initialize();
    }).not.toThrow();
  });

  it('should handle shutdown gracefully', async () => {
    const testTelemetry = new EnhancedTelemetry({
      serviceName: 'test-shutdown',
      enableMetrics: false,
      enableTracing: false,
    });

    testTelemetry.initialize();

    await expect(testTelemetry.shutdown()).resolves.not.toThrow();
  });

  it('should handle errors in metric collection gracefully', () => {
    // Test that metric collection errors don't crash the application
    const originalConsoleError = console.error;
    const errorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    // This should not throw even if there are internal errors
    expect(() => {
      telemetry.recordCounter('test.error.counter', 1);
      telemetry.recordGauge('test.error.gauge', 42);
    }).not.toThrow();

    errorSpy.mockRestore();
  });
});