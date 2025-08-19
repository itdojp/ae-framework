/**
 * Integration tests for the complete resilience system
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  BackoffStrategy,
  CircuitBreaker,
  CircuitState,
  TokenBucketRateLimiter,
} from '../../src/resilience/backoff-strategies.js';
import { Bulkhead } from '../../src/resilience/bulkhead-isolation.js';
import { TimeoutWrapper } from '../../src/resilience/timeout-patterns.js';

describe('Resilience System Integration', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Combined Patterns', () => {
    it('should handle a complete resilience scenario', async () => {
      // Setup components
      const backoffStrategy = new BackoffStrategy({
        maxRetries: 3,
        baseDelayMs: 10,
        shouldRetry: () => true,
      });

      const circuitBreaker = new CircuitBreaker({
        failureThreshold: 2,
        recoveryTimeout: 1000,
        monitoringPeriod: 5000,
      });

      const rateLimiter = new TokenBucketRateLimiter({
        tokensPerInterval: 5,
        interval: 1000,
        maxTokens: 5,
      });

      const bulkhead = new Bulkhead({
        name: 'test-bulkhead',
        maxConcurrent: 2,
        maxQueued: 2,
        timeoutMs: 5000,
      });

      const timeoutWrapper = new TimeoutWrapper({
        timeoutMs: 1000,
      });

      // Test successful operation flow
      let operationCalls = 0;
      const successfulOperation = async () => {
        operationCalls++;
        await rateLimiter.waitForTokens();
        return `Success ${operationCalls}`;
      };

      // Wrap operation with all resilience patterns
      const resilientOperation = async () => {
        return await bulkhead.execute(async () => {
          return await circuitBreaker.execute(async () => {
            return await timeoutWrapper.execute(successfulOperation);
          });
        });
      };

      const result = await backoffStrategy.executeWithRetry(resilientOperation);

      expect(result.success).toBe(true);
      expect(result.result).toBe('Success 1');
      expect(operationCalls).toBe(1);

      // Verify component states
      expect(circuitBreaker.getStats().state).toBe(CircuitState.CLOSED);
      expect(circuitBreaker.getStats().successes).toBe(1);
      expect(rateLimiter.getTokenCount()).toBe(4); // 5 - 1 consumed
      expect(bulkhead.getStats().totalExecuted).toBe(1);
    });

    it('should handle cascading failures gracefully', async () => {
      const backoffStrategy = new BackoffStrategy({
        maxRetries: 2,
        baseDelayMs: 1,
        shouldRetry: () => true,
      });

      const circuitBreaker = new CircuitBreaker({
        failureThreshold: 1,
        recoveryTimeout: 1000,
        monitoringPeriod: 5000,
      });

      let attemptCount = 0;
      const failingOperation = async () => {
        attemptCount++;
        throw new Error(`Failure ${attemptCount}`);
      };

      // First attempt should fail and open circuit
      const resilientOperation = async () => {
        return await circuitBreaker.execute(failingOperation);
      };

      const result = await backoffStrategy.executeWithRetry(resilientOperation);

      expect(result.success).toBe(false);
      expect(circuitBreaker.getStats().state).toBe(CircuitState.OPEN);
      expect(circuitBreaker.getStats().failures).toBe(1);
      
      // Subsequent calls should fail fast due to open circuit
      await expect(circuitBreaker.execute(failingOperation))
        .rejects.toThrow('Circuit breaker is OPEN');
    });

    it('should demonstrate rate limiting with bulkhead isolation', async () => {
      const rateLimiter = new TokenBucketRateLimiter({
        tokensPerInterval: 2,
        interval: 1000,
        maxTokens: 2,
      });

      const bulkhead = new Bulkhead({
        name: 'rate-limited-bulkhead',
        maxConcurrent: 1,
        maxQueued: 1,
        timeoutMs: 2000,
      });

      let completedOperations = 0;
      const rateLimitedOperation = async () => {
        await rateLimiter.waitForTokens();
        completedOperations++;
        return `Operation ${completedOperations}`;
      };

      // Start multiple operations
      const operations = [
        bulkhead.execute(rateLimitedOperation),
        bulkhead.execute(rateLimitedOperation),
      ];

      // Third operation should be queued
      const queuedOperation = bulkhead.execute(rateLimitedOperation);

      const results = await Promise.all([
        ...operations,
        queuedOperation,
      ]);

      expect(results).toHaveLength(3);
      expect(completedOperations).toBe(3);
      expect(bulkhead.getStats().totalExecuted).toBe(3);
      expect(rateLimiter.getTokenCount()).toBe(0); // All tokens consumed
    });
  });

  describe('Error Recovery Scenarios', () => {
    it('should recover from temporary failures', async () => {
      const backoffStrategy = new BackoffStrategy({
        maxRetries: 3,
        baseDelayMs: 1,
        shouldRetry: () => true,
      });

      const circuitBreaker = new CircuitBreaker({
        failureThreshold: 3,
        recoveryTimeout: 100,
        monitoringPeriod: 5000,
      });

      let attemptCount = 0;
      const flakyOperation = async () => {
        attemptCount++;
        if (attemptCount <= 2) {
          throw new Error(`Temporary failure ${attemptCount}`);
        }
        return 'Success after recovery';
      };

      const resilientOperation = async () => {
        return await circuitBreaker.execute(flakyOperation);
      };

      const result = await backoffStrategy.executeWithRetry(resilientOperation);

      expect(result.success).toBe(true);
      expect(result.result).toBe('Success after recovery');
      expect(result.attempts).toBe(3);
      expect(attemptCount).toBe(3);
      expect(circuitBreaker.getStats().state).toBe(CircuitState.CLOSED);
    });

    it('should handle timeout recovery', async () => {
      const timeoutWrapper = new TimeoutWrapper({
        timeoutMs: 50,
      });

      let operationDuration = 100; // Start with timeout-causing duration
      const adaptiveOperation = async () => {
        await new Promise(resolve => setTimeout(resolve, operationDuration));
        return 'Completed';
      };

      // First call should timeout
      await expect(timeoutWrapper.execute(adaptiveOperation))
        .rejects.toThrow('timed out');

      // Reduce operation duration to simulate recovery
      operationDuration = 25;

      // Second call should succeed
      const result = await timeoutWrapper.execute(adaptiveOperation);
      expect(result).toBe('Completed');
    });
  });

  describe('Performance and Monitoring', () => {
    it('should track comprehensive metrics across all components', async () => {
      const backoffStrategy = new BackoffStrategy({
        maxRetries: 1,
        baseDelayMs: 1,
        shouldRetry: () => true,
      });

      const circuitBreaker = new CircuitBreaker({
        failureThreshold: 5,
        recoveryTimeout: 1000,
        monitoringPeriod: 5000,
      });

      const bulkhead = new Bulkhead({
        name: 'metrics-bulkhead',
        maxConcurrent: 3,
        maxQueued: 2,
        timeoutMs: 1000,
      });

      // Run mixed success/failure operations
      const operations = [];
      for (let i = 0; i < 5; i++) {
        const operation = async () => {
          const shouldFail = i % 2 === 0;
          if (shouldFail) {
            throw new Error(`Planned failure ${i}`);
          }
          return `Success ${i}`;
        };

        const resilientOp = async () => {
          return await bulkhead.execute(async () => {
            return await circuitBreaker.execute(operation);
          });
        };

        operations.push(
          backoffStrategy.executeWithRetry(resilientOp).catch(error => ({ error }))
        );
      }

      const results = await Promise.all(operations);

      // Verify metrics collection
      const cbStats = circuitBreaker.getStats();
      const bulkheadStats = bulkhead.getStats();

      expect(cbStats.totalRequests).toBeGreaterThan(0);
      expect(cbStats.failures + cbStats.successes).toBe(cbStats.totalRequests);
      expect(bulkheadStats.totalExecuted + bulkheadStats.totalRejected).toBeGreaterThan(0);
      
      // Verify some operations succeeded and some failed
      const successes = results.filter(r => !('error' in r));
      const failures = results.filter(r => 'error' in r);
      
      expect(successes.length).toBeGreaterThan(0);
      expect(failures.length).toBeGreaterThan(0);
    });
  });
});