import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { CircuitBreaker, CircuitBreakerManager, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker.js';

describe('CircuitBreaker', () => {
  let circuitBreaker: CircuitBreaker;

  beforeEach(() => {
    circuitBreaker = new CircuitBreaker('test-breaker', {
      failureThreshold: 3,
      successThreshold: 2,
      timeout: 1000,
      monitoringWindow: 5000,
      enableMonitoring: true
    });
  });

  afterEach(() => {
    circuitBreaker.removeAllListeners();
  });

  describe('Basic Functionality', () => {
    it('should start in CLOSED state', () => {
      expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
      expect(circuitBreaker.getName()).toBe('test-breaker');
      expect(circuitBreaker.isHealthy()).toBe(true);
    });

    it('should execute successful operations', async () => {
      const operation = vi.fn().mockResolvedValue('success');
      
      const result = await circuitBreaker.execute(operation);
      
      expect(result).toBe('success');
      expect(operation).toHaveBeenCalledOnce();
      expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
      
      const stats = circuitBreaker.getStats();
      expect(stats.totalRequests).toBe(1);
      expect(stats.totalSuccesses).toBe(1);
      expect(stats.totalFailures).toBe(0);
    });

    it('should handle operation failures', async () => {
      const operation = vi.fn().mockRejectedValue(new Error('Test error'));
      
      await expect(circuitBreaker.execute(operation)).rejects.toThrow('Test error');
      
      expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
      
      const stats = circuitBreaker.getStats();
      expect(stats.totalRequests).toBe(1);
      expect(stats.totalFailures).toBe(1);
      expect(stats.failureCount).toBe(1);
    });

    it('should execute synchronous operations', () => {
      const operation = vi.fn().mockReturnValue('sync success');
      
      const result = circuitBreaker.executeSync(operation);
      
      expect(result).toBe('sync success');
      expect(operation).toHaveBeenCalledOnce();
      expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
    });
  });

  describe('Circuit Opening', () => {
    it('should open circuit after failure threshold is reached', async () => {
      const operation = vi.fn().mockRejectedValue(new Error('Test error'));
      
      // Perform failures up to threshold
      for (let i = 0; i < 3; i++) {
        await expect(circuitBreaker.execute(operation)).rejects.toThrow('Test error');
      }
      
      expect(circuitBreaker.getState()).toBe(CircuitState.OPEN);
      
      const stats = circuitBreaker.getStats();
      expect(stats.circuitOpenCount).toBe(1);
    });

    it('should reject calls immediately when circuit is open', async () => {
      // Create circuit breaker without fallback for this test
      const testBreaker = new CircuitBreaker('no-fallback-test', {
        failureThreshold: 1,
        fallback: undefined // Explicitly no fallback
      });
      
      // Force circuit open
      testBreaker.forceOpen();
      
      const operation = vi.fn().mockResolvedValue('success');
      
      await expect(testBreaker.execute(operation)).rejects.toThrow(CircuitBreakerOpenError);
      expect(operation).not.toHaveBeenCalled();
    });

    it('should use fallback when circuit is open', async () => {
      const fallback = vi.fn().mockReturnValue('fallback result');
      const breakerWithFallback = new CircuitBreaker('fallback-test', {
        failureThreshold: 1,
        fallback
      });
      
      // Force circuit open
      breakerWithFallback.forceOpen();
      
      const operation = vi.fn().mockResolvedValue('success');
      const result = await breakerWithFallback.execute(operation);
      
      expect(result).toBe('fallback result');
      expect(fallback).toHaveBeenCalled();
      expect(operation).not.toHaveBeenCalled();
    });
  });

  describe('Circuit Recovery', () => {
    it('should transition to half-open after timeout', async () => {
      // Create breaker with short timeout for testing
      const quickBreaker = new CircuitBreaker('quick-test', {
        failureThreshold: 1,
        timeout: 100 // 100ms timeout
      });
      
      // Force circuit open
      quickBreaker.forceOpen();
      expect(quickBreaker.getState()).toBe(CircuitState.OPEN);
      
      // Wait for timeout
      await new Promise(resolve => setTimeout(resolve, 150));
      
      // Next operation should transition to half-open
      const operation = vi.fn().mockResolvedValue('success');
      await quickBreaker.execute(operation);
      
      expect(quickBreaker.getState()).toBe(CircuitState.HALF_OPEN);
    });

    it('should close circuit after success threshold in half-open state', async () => {
      // Set up circuit in half-open state
      circuitBreaker.forceOpen();
      
      // Create short timeout breaker for testing
      const testBreaker = new CircuitBreaker('recovery-test', {
        failureThreshold: 3,
        successThreshold: 2,
        timeout: 50
      });
      
      testBreaker.forceOpen();
      
      // Wait for timeout to allow half-open transition
      await new Promise(resolve => setTimeout(resolve, 100));
      
      const operation = vi.fn().mockResolvedValue('success');
      
      // First success should move to half-open
      await testBreaker.execute(operation);
      expect(testBreaker.getState()).toBe(CircuitState.HALF_OPEN);
      
      // Second success should close the circuit
      await testBreaker.execute(operation);
      expect(testBreaker.getState()).toBe(CircuitState.CLOSED);
    });

    it('should return to open state if failure occurs in half-open', async () => {
      const testBreaker = new CircuitBreaker('half-open-fail-test', {
        failureThreshold: 1,
        timeout: 50
      });
      
      // Force open and wait for timeout
      testBreaker.forceOpen();
      await new Promise(resolve => setTimeout(resolve, 100));
      
      // First call should transition to half-open, then fail
      const operation = vi.fn().mockRejectedValue(new Error('Half-open failure'));
      
      await expect(testBreaker.execute(operation)).rejects.toThrow('Half-open failure');
      expect(testBreaker.getState()).toBe(CircuitState.OPEN);
    });
  });

  describe('Statistics and Monitoring', () => {
    it('should track comprehensive statistics', async () => {
      const successOp = vi.fn().mockResolvedValue('success');
      const failOp = vi.fn().mockRejectedValue(new Error('fail'));
      
      // Perform some operations
      await circuitBreaker.execute(successOp);
      await circuitBreaker.execute(successOp);
      await expect(circuitBreaker.execute(failOp)).rejects.toThrow();
      
      const stats = circuitBreaker.getStats();
      
      expect(stats.totalRequests).toBe(3);
      expect(stats.totalSuccesses).toBe(2);
      expect(stats.totalFailures).toBe(1);
      expect(stats.state).toBe(CircuitState.CLOSED);
      expect(stats.lastSuccessTime).toBeTruthy();
      expect(stats.lastFailureTime).toBeTruthy();
      expect(stats.uptime).toBeGreaterThanOrEqual(0);
    });

    it('should calculate average response time', async () => {
      const operation = vi.fn().mockImplementation(async () => {
        await new Promise(resolve => setTimeout(resolve, 100));
        return 'success';
      });
      
      await circuitBreaker.execute(operation);
      await circuitBreaker.execute(operation);
      
      const stats = circuitBreaker.getStats();
      expect(stats.averageResponseTime).toBeGreaterThan(90); // Account for timing variations
    });

    it('should determine health status correctly', async () => {
      expect(circuitBreaker.isHealthy()).toBe(true);
      
      // Force circuit open
      circuitBreaker.forceOpen();
      expect(circuitBreaker.isHealthy()).toBe(false);
      
      // Reset to closed
      circuitBreaker.forceClose();
      expect(circuitBreaker.isHealthy()).toBe(true);
    });
  });

  describe('Health Report Generation', () => {
    it('should generate comprehensive health report', async () => {
      const successOp = vi.fn().mockResolvedValue('success');
      const failOp = vi.fn().mockRejectedValue(new Error('Test failure'));
      
      // Perform some operations
      await circuitBreaker.execute(successOp);
      await expect(circuitBreaker.execute(failOp)).rejects.toThrow();
      
      const report = circuitBreaker.generateHealthReport();
      
      expect(report.name).toBe('test-breaker');
      expect(report.state).toBe(CircuitState.CLOSED);
      expect(report.health).toBe('degraded'); // Health is degraded due to recent failure
      expect(report.stats).toBeDefined();
      expect(report.recentFailures).toHaveLength(1);
      expect(report.recommendations).toBeInstanceOf(Array);
    });

    it('should provide recommendations for unhealthy circuits', () => {
      circuitBreaker.forceOpen();
      
      const report = circuitBreaker.generateHealthReport();
      
      expect(report.health).toBe('unhealthy');
      expect(report.recommendations.length).toBeGreaterThan(0);
      expect(report.recommendations).toContain('Circuit is open - check underlying service health');
    });
  });

  describe('Manual Control', () => {
    it('should allow forcing circuit open', () => {
      circuitBreaker.forceOpen();
      expect(circuitBreaker.getState()).toBe(CircuitState.OPEN);
    });

    it('should allow forcing circuit closed', () => {
      circuitBreaker.forceOpen();
      circuitBreaker.forceClose();
      expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
    });

    it('should reset circuit to initial state', async () => {
      // Perform some operations to change state
      const failOp = vi.fn().mockRejectedValue(new Error('fail'));
      await expect(circuitBreaker.execute(failOp)).rejects.toThrow();
      
      const beforeReset = circuitBreaker.getStats();
      expect(beforeReset.totalRequests).toBe(1);
      
      circuitBreaker.reset();
      
      const afterReset = circuitBreaker.getStats();
      expect(afterReset.totalRequests).toBe(0);
      expect(afterReset.totalFailures).toBe(0);
      expect(afterReset.failureCount).toBe(0);
      expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
    });
  });

  describe('Event Emission', () => {
    it('should emit circuit opened event', async () => {
      const openedHandler = vi.fn();
      circuitBreaker.on('circuitOpened', openedHandler);
      
      const failOp = vi.fn().mockRejectedValue(new Error('fail'));
      
      // Trigger failures to open circuit
      for (let i = 0; i < 3; i++) {
        await expect(circuitBreaker.execute(failOp)).rejects.toThrow();
      }
      
      expect(openedHandler).toHaveBeenCalledWith({
        name: 'test-breaker',
        failureCount: 3,
        threshold: 3,
        timeout: 1000
      });
    });

    it('should emit circuit closed event', () => {
      const closedHandler = vi.fn();
      circuitBreaker.on('circuitClosed', closedHandler);
      
      // Force open then close
      circuitBreaker.forceOpen();
      circuitBreaker.forceClose();
      
      expect(closedHandler).toHaveBeenCalled();
    });

    it('should emit state change events', () => {
      const stateChangeHandler = vi.fn();
      circuitBreaker.on('stateChanged', stateChangeHandler);
      
      circuitBreaker.forceOpen();
      
      expect(stateChangeHandler).toHaveBeenCalledWith(
        expect.objectContaining({
          name: 'test-breaker',
          previousState: CircuitState.CLOSED,
          newState: CircuitState.OPEN
        })
      );
    });

    it('should emit operation success and failure events', async () => {
      const successHandler = vi.fn();
      const failureHandler = vi.fn();
      
      circuitBreaker.on('operationSuccess', successHandler);
      circuitBreaker.on('operationFailure', failureHandler);
      
      const successOp = vi.fn().mockResolvedValue('success');
      const failOp = vi.fn().mockRejectedValue(new Error('fail'));
      
      await circuitBreaker.execute(successOp);
      await expect(circuitBreaker.execute(failOp)).rejects.toThrow();
      
      expect(successHandler).toHaveBeenCalled();
      expect(failureHandler).toHaveBeenCalled();
    });
  });

  describe('Error Type Filtering', () => {
    it('should only trip on expected error types when specified', async () => {
      class NetworkError extends Error {
        constructor(message: string) {
          super(message);
          this.name = 'NetworkError';
        }
      }
      
      class ValidationError extends Error {
        constructor(message: string) {
          super(message);
          this.name = 'ValidationError';
        }
      }
      
      const selectiveBreaker = new CircuitBreaker('selective-breaker', {
        failureThreshold: 2,
        expectedErrors: [NetworkError]
      });
      
      // ValidationError should not count towards failure threshold
      const validationOp = vi.fn().mockRejectedValue(new ValidationError('Validation failed'));
      const networkOp = vi.fn().mockRejectedValue(new NetworkError('Network failed'));
      
      // Multiple validation errors should not open circuit
      await expect(selectiveBreaker.execute(validationOp)).rejects.toThrow();
      await expect(selectiveBreaker.execute(validationOp)).rejects.toThrow();
      await expect(selectiveBreaker.execute(validationOp)).rejects.toThrow();
      
      expect(selectiveBreaker.getState()).toBe(CircuitState.CLOSED);
      
      // Network errors should count and open circuit
      await expect(selectiveBreaker.execute(networkOp)).rejects.toThrow();
      await expect(selectiveBreaker.execute(networkOp)).rejects.toThrow();
      
      expect(selectiveBreaker.getState()).toBe(CircuitState.OPEN);
    });
  });
});

describe('CircuitBreakerManager', () => {
  let manager: CircuitBreakerManager;

  beforeEach(() => {
    manager = new CircuitBreakerManager();
  });

  afterEach(() => {
    manager.removeAllListeners();
  });

  describe('Circuit Breaker Management', () => {
    it('should create and retrieve circuit breakers', () => {
      const breaker1 = manager.getCircuitBreaker('test-1');
      const breaker2 = manager.getCircuitBreaker('test-2');
      
      expect(breaker1.getName()).toBe('test-1');
      expect(breaker2.getName()).toBe('test-2');
      expect(breaker1).not.toBe(breaker2);
      
      // Getting same name should return same instance
      const breaker1Again = manager.getCircuitBreaker('test-1');
      expect(breaker1Again).toBe(breaker1);
    });

    it('should get all circuit breakers', () => {
      manager.getCircuitBreaker('test-1');
      manager.getCircuitBreaker('test-2');
      manager.getCircuitBreaker('test-3');
      
      const allBreakers = manager.getAllBreakers();
      expect(allBreakers.size).toBe(3);
      expect(allBreakers.has('test-1')).toBe(true);
      expect(allBreakers.has('test-2')).toBe(true);
      expect(allBreakers.has('test-3')).toBe(true);
    });

    it('should remove circuit breakers', () => {
      manager.getCircuitBreaker('test-1');
      manager.getCircuitBreaker('test-2');
      
      const removed = manager.removeCircuitBreaker('test-1');
      expect(removed).toBe(true);
      
      const allBreakers = manager.getAllBreakers();
      expect(allBreakers.size).toBe(1);
      expect(allBreakers.has('test-1')).toBe(false);
      expect(allBreakers.has('test-2')).toBe(true);
      
      // Removing non-existent breaker should return false
      const removedAgain = manager.removeCircuitBreaker('test-1');
      expect(removedAgain).toBe(false);
    });

    it('should reset all circuit breakers', async () => {
      const breaker1 = manager.getCircuitBreaker('test-1');
      const breaker2 = manager.getCircuitBreaker('test-2');
      
      // Generate some activity
      const failOp = vi.fn().mockRejectedValue(new Error('fail'));
      await expect(breaker1.execute(failOp)).rejects.toThrow();
      await expect(breaker2.execute(failOp)).rejects.toThrow();
      
      expect(breaker1.getStats().totalRequests).toBe(1);
      expect(breaker2.getStats().totalRequests).toBe(1);
      
      manager.resetAll();
      
      expect(breaker1.getStats().totalRequests).toBe(0);
      expect(breaker2.getStats().totalRequests).toBe(0);
    });
  });

  describe('Global Statistics', () => {
    it('should track global statistics', async () => {
      const breaker1 = manager.getCircuitBreaker('test-1', { failureThreshold: 1 });
      const breaker2 = manager.getCircuitBreaker('test-2', { failureThreshold: 1 });
      
      const successOp = vi.fn().mockResolvedValue('success');
      const failOp = vi.fn().mockRejectedValue(new Error('fail'));
      
      // Generate mixed activity
      await breaker1.execute(successOp);
      await expect(breaker1.execute(failOp)).rejects.toThrow(); // Opens circuit
      await breaker2.execute(successOp);
      
      const stats = manager.getGlobalStats();
      
      expect(stats.totalBreakers).toBe(2);
      expect(stats.openBreakers).toBe(1);
      expect(stats.closedBreakers).toBe(1);
      expect(stats.halfOpenBreakers).toBe(0);
      expect(stats.totalRequests).toBe(3);
      expect(stats.totalFailures).toBe(1);
      expect(stats.breakers).toHaveLength(2);
    });
  });

  describe('Health Reporting', () => {
    it('should generate comprehensive health report', async () => {
      const breaker1 = manager.getCircuitBreaker('healthy-breaker');
      const breaker2 = manager.getCircuitBreaker('unhealthy-breaker', { failureThreshold: 1 });
      
      const successOp = vi.fn().mockResolvedValue('success');
      const failOp = vi.fn().mockRejectedValue(new Error('Critical failure'));
      
      // Keep one healthy, make one unhealthy
      await breaker1.execute(successOp);
      await expect(breaker2.execute(failOp)).rejects.toThrow();
      
      const healthReport = manager.generateHealthReport();
      
      expect(healthReport.overall).toBe('unhealthy'); // Because one breaker is open
      expect(healthReport.summary.totalBreakers).toBe(2);
      expect(healthReport.summary.openBreakers).toBe(1);
      expect(healthReport.summary.closedBreakers).toBe(1);
      expect(healthReport.breakers).toHaveLength(2);
      
      const healthyBreaker = healthReport.breakers.find(b => b.name === 'healthy-breaker');
      const unhealthyBreaker = healthReport.breakers.find(b => b.name === 'unhealthy-breaker');
      
      expect(healthyBreaker?.health).toBe('healthy');
      expect(unhealthyBreaker?.health).toBe('unhealthy');
      expect(unhealthyBreaker?.recommendations.length).toBeGreaterThan(0);
    });

    it('should determine overall health correctly', async () => {
      const breaker1 = manager.getCircuitBreaker('test-1');
      const breaker2 = manager.getCircuitBreaker('test-2');
      
      // All healthy
      let report = manager.generateHealthReport();
      expect(report.overall).toBe('healthy');
      
      // Make one degraded (half-open)
      breaker1.forceOpen();
      
      // Create short timeout breaker to test half-open
      const quickBreaker = manager.getCircuitBreaker('quick-test', { timeout: 50 });
      quickBreaker.forceOpen();
      
      await new Promise(resolve => setTimeout(resolve, 100));
      
      // Trigger half-open state
      const successOp = vi.fn().mockResolvedValue('success');
      await quickBreaker.execute(successOp);
      
      report = manager.generateHealthReport();
      expect(report.overall).toBe('unhealthy'); // Open breaker makes it unhealthy
    });
  });

  describe('Event Forwarding', () => {
    it('should forward events from individual circuit breakers', async () => {
      const stateChangeHandler = vi.fn();
      const circuitOpenedHandler = vi.fn();
      const circuitClosedHandler = vi.fn();
      
      manager.on('breakerStateChanged', stateChangeHandler);
      manager.on('circuitOpened', circuitOpenedHandler);
      manager.on('circuitClosed', circuitClosedHandler);
      
      const breaker = manager.getCircuitBreaker('event-test', { failureThreshold: 1 });
      
      // Trigger circuit open
      const failOp = vi.fn().mockRejectedValue(new Error('fail'));
      await expect(breaker.execute(failOp)).rejects.toThrow();
      
      expect(stateChangeHandler).toHaveBeenCalled();
      expect(circuitOpenedHandler).toHaveBeenCalled();
      
      // Trigger circuit close
      breaker.forceClose();
      
      expect(circuitClosedHandler).toHaveBeenCalled();
    });
  });
});