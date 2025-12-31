/**
 * Simple tests to verify core resilience functionality
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  BackoffStrategy,
  CircuitBreaker,
  CircuitState,
  TokenBucketRateLimiter,
} from '../../src/resilience/backoff-strategies.js';

describe('Resilience Core Functionality', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('BackoffStrategy Basic Functionality', () => {
    it('should execute successful operation immediately', async () => {
      const backoffStrategy = new BackoffStrategy({
        maxRetries: 3,
        baseDelayMs: 100,
        shouldRetry: () => true,
      });

      const operation = vi.fn().mockResolvedValue('success');
      const result = await backoffStrategy.executeWithRetry(operation);

      expect(result.success).toBe(true);
      expect(result.result).toBe('success');
      expect(result.attempts).toBe(1);
      expect(operation).toHaveBeenCalledTimes(1);
    });

    it('should retry failed operations', async () => {
      const backoffStrategy = new BackoffStrategy({
        maxRetries: 2,
        baseDelayMs: 1, // Very short delay for test
        shouldRetry: () => true,
      });

      const operation = vi.fn()
        .mockRejectedValueOnce(new Error('Failed once'))
        .mockResolvedValue('success');

      const result = await backoffStrategy.executeWithRetry(operation);

      expect(result.success).toBe(true);
      expect(result.result).toBe('success');
      expect(result.attempts).toBe(2);
      expect(operation).toHaveBeenCalledTimes(2);
    });

    it('should respect max retries', async () => {
      const backoffStrategy = new BackoffStrategy({
        maxRetries: 1,
        baseDelayMs: 1,
        shouldRetry: () => true,
      });

      const operation = vi.fn().mockRejectedValue(new Error('Always fails'));

      const result = await backoffStrategy.executeWithRetry(operation);

      expect(result.success).toBe(false);
      expect(result.error?.message).toBe('Always fails');
      expect(result.attempts).toBe(2); // 1 initial + 1 retry
      expect(operation).toHaveBeenCalledTimes(2);
    });
  });

  describe('CircuitBreaker Basic Functionality', () => {
    it('should start in CLOSED state', () => {
      const circuitBreaker = new CircuitBreaker({
        failureThreshold: 3,
        recoveryTimeout: 1000,
        monitoringPeriod: 5000,
      });

      expect(circuitBreaker.getStats().state).toBe(CircuitState.CLOSED);
    });

    it('should execute successful operations in CLOSED state', async () => {
      const circuitBreaker = new CircuitBreaker({
        failureThreshold: 3,
        recoveryTimeout: 1000,
        monitoringPeriod: 5000,
      });

      const operation = vi.fn().mockResolvedValue('success');
      const result = await circuitBreaker.execute(operation);

      expect(result).toBe('success');
      expect(circuitBreaker.getStats().state).toBe(CircuitState.CLOSED);
      expect(circuitBreaker.getStats().successes).toBe(1);
    });

    it('should open after reaching failure threshold', async () => {
      const circuitBreaker = new CircuitBreaker({
        failureThreshold: 2,
        recoveryTimeout: 1000,
        monitoringPeriod: 5000,
      });

      const operation = vi.fn().mockRejectedValue(new Error('Service error'));

      // First failure
      try {
        await circuitBreaker.execute(operation);
      } catch {}

      expect(circuitBreaker.getStats().state).toBe(CircuitState.CLOSED);

      // Second failure should open circuit
      try {
        await circuitBreaker.execute(operation);
      } catch {}

      expect(circuitBreaker.getStats().state).toBe(CircuitState.OPEN);
      expect(circuitBreaker.getStats().failures).toBe(2);
    });
  });

  describe('TokenBucketRateLimiter Basic Functionality', () => {
    it('should start with full token bucket', () => {
      const rateLimiter = new TokenBucketRateLimiter({
        tokensPerInterval: 10,
        interval: 1000,
        maxTokens: 10,
      });

      expect(rateLimiter.getTokenCount()).toBe(10);
    });

    it('should consume tokens successfully', async () => {
      const rateLimiter = new TokenBucketRateLimiter({
        tokensPerInterval: 10,
        interval: 1000,
        maxTokens: 10,
      });

      const result = await rateLimiter.consume(3);
      expect(result).toBe(true);
      expect(rateLimiter.getTokenCount()).toBe(7);
    });

    it('should reject when insufficient tokens', async () => {
      const rateLimiter = new TokenBucketRateLimiter({
        tokensPerInterval: 10,
        interval: 1000,
        maxTokens: 10,
      });

      await rateLimiter.consume(8);
      const result = await rateLimiter.consume(5);
      expect(result).toBe(false);
      expect(rateLimiter.getTokenCount()).toBe(2);
    });
  });
});
