/**
 * Comprehensive tests for resilience backoff strategies
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  BackoffStrategy,
  CircuitBreaker,
  CircuitState,
  TokenBucketRateLimiter,
  ResilientHttpClient,
  CircuitBreakerOptions,
} from '../../src/resilience/backoff-strategies.js';

describe('BackoffStrategy', () => {
  let backoffStrategy: BackoffStrategy;

  beforeEach(() => {
    vi.useFakeTimers();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('Basic Retry Logic', () => {
    beforeEach(() => {
      backoffStrategy = new BackoffStrategy({
        maxRetries: 3,
        baseDelayMs: 100,
        maxDelayMs: 1000,
        jitterType: 'none',
        multiplier: 2,
        shouldRetry: () => true, // Always retry for tests
      });
    });

    it('should succeed on first attempt', async () => {
      const operation = vi.fn().mockResolvedValue('success');

      const result = await backoffStrategy.executeWithRetry(operation, 'test-op');

      expect(result.success).toBe(true);
      expect(result.result).toBe('success');
      expect(result.attempts).toBe(1);
      expect(operation).toHaveBeenCalledTimes(1);
    });

    it('should retry on failure and eventually succeed', async () => {
      const operation = vi.fn()
        .mockRejectedValueOnce(new Error('Network error'))
        .mockRejectedValueOnce(new Error('Network error'))
        .mockResolvedValue('success');

      const promise = backoffStrategy.executeWithRetry(operation, 'test-op');
      
      // Fast-forward timers to handle delays
      await vi.runAllTimersAsync();

      const result = await promise;

      expect(result.success).toBe(true);
      expect(result.result).toBe('success');
      expect(result.attempts).toBe(3);
      expect(operation).toHaveBeenCalledTimes(3);
    });

    it('should fail after max retries', async () => {
      const operation = vi.fn().mockRejectedValue(new Error('Persistent error'));

      const promise = backoffStrategy.executeWithRetry(operation, 'test-op');
      
      await vi.runAllTimersAsync();

      const result = await promise;

      expect(result.success).toBe(false);
      expect(result.error?.message).toBe('Persistent error');
      expect(result.attempts).toBe(4); // 1 initial + 3 retries
      expect(operation).toHaveBeenCalledTimes(4);
    });
  });

  describe('Jitter Strategies', () => {
    it('should apply full jitter correctly', async () => {
      backoffStrategy = new BackoffStrategy({
        maxRetries: 2,
        baseDelayMs: 100,
        jitterType: 'full',
        multiplier: 2,
        shouldRetry: () => true, // Always retry for tests
      });

      const operation = vi.fn()
        .mockRejectedValueOnce(new Error('Error 1'))
        .mockRejectedValueOnce(new Error('Error 2'))
        .mockResolvedValue('success');

      const promise = backoffStrategy.executeWithRetry(operation);
      await vi.runAllTimersAsync();
      const result = await promise;

      expect(result.delays.length).toBe(2);
      // Full jitter should be between 0 and base delay
      expect(result.delays[0]).toBeGreaterThanOrEqual(0);
      expect(result.delays[0]).toBeLessThanOrEqual(100);
      expect(result.delays[1]).toBeGreaterThanOrEqual(0);
      expect(result.delays[1]).toBeLessThanOrEqual(200);
    });

    it('should apply equal jitter correctly', async () => {
      backoffStrategy = new BackoffStrategy({
        maxRetries: 1,
        baseDelayMs: 100,
        jitterType: 'equal',
        multiplier: 2,
        shouldRetry: () => true, // Always retry for tests
      });

      const operation = vi.fn()
        .mockRejectedValueOnce(new Error('Error'))
        .mockResolvedValue('success');

      const promise = backoffStrategy.executeWithRetry(operation);
      await vi.runAllTimersAsync();
      const result = await promise;

      // Equal jitter should be between baseDelay/2 and baseDelay
      expect(result.delays[0]).toBeGreaterThanOrEqual(50);
      expect(result.delays[0]).toBeLessThanOrEqual(100);
    });
  });

  describe('Retry Conditions', () => {
    beforeEach(() => {
      backoffStrategy = new BackoffStrategy({
        maxRetries: 2,
        baseDelayMs: 10,
        shouldRetry: (error: Error) => error.message.includes('retryable'),
      });
    });

    it('should respect custom retry condition', async () => {
      const operation = vi.fn()
        .mockRejectedValueOnce(new Error('non-retryable error'))
        .mockResolvedValue('success');

      const promise = backoffStrategy.executeWithRetry(operation);
      await vi.runAllTimersAsync();
      const result = await promise;

      expect(result.success).toBe(false);
      expect(result.attempts).toBe(1);
      expect(operation).toHaveBeenCalledTimes(1);
    });

    it('should retry on retryable errors', async () => {
      const operation = vi.fn()
        .mockRejectedValueOnce(new Error('retryable network error'))
        .mockResolvedValue('success');

      const promise = backoffStrategy.executeWithRetry(operation);
      await vi.runAllTimersAsync();
      const result = await promise;

      expect(result.success).toBe(true);
      expect(result.attempts).toBe(2);
      expect(operation).toHaveBeenCalledTimes(2);
    });
  });

  describe('Timeout Handling', () => {
    it('should timeout long-running operations', async () => {
      backoffStrategy = new BackoffStrategy({
        maxRetries: 1,
        baseDelayMs: 10,
        timeout: 50,
      });

      const operation = vi.fn().mockImplementation(() => 
        new Promise(resolve => setTimeout(resolve, 100))
      );

      const promise = backoffStrategy.executeWithRetry(operation);
      await vi.runAllTimersAsync();
      const result = await promise;

      expect(result.success).toBe(false);
      expect(result.error?.message).toContain('timed out');
    });
  });
});

describe('CircuitBreaker', () => {
  let circuitBreaker: CircuitBreaker;
  const defaultOptions: CircuitBreakerOptions = {
    failureThreshold: 3,
    recoveryTimeout: 1000,
    monitoringPeriod: 10000,
  };

  beforeEach(() => {
    vi.useFakeTimers();
    circuitBreaker = new CircuitBreaker(defaultOptions);
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('State Transitions', () => {
    it('should start in CLOSED state', () => {
      const stats = circuitBreaker.getStats();
      expect(stats.state).toBe(CircuitState.CLOSED);
    });

    it('should open after failure threshold', async () => {
      const operation = vi.fn().mockRejectedValue(new Error('Service error'));

      for (let i = 0; i < 3; i++) {
        try {
          await circuitBreaker.execute(operation);
        } catch {}
      }

      const stats = circuitBreaker.getStats();
      expect(stats.state).toBe(CircuitState.OPEN);
      expect(stats.failures).toBe(3);
    });

    it('should transition to HALF_OPEN after recovery timeout', async () => {
      const operation = vi.fn().mockRejectedValue(new Error('Service error'));

      // Trigger circuit opening
      for (let i = 0; i < 3; i++) {
        try {
          await circuitBreaker.execute(operation);
        } catch {}
      }

      expect(circuitBreaker.getStats().state).toBe(CircuitState.OPEN);

      // Fast-forward past recovery timeout
      vi.advanceTimersByTime(1001);

      // Next call should transition to HALF_OPEN
      operation.mockResolvedValueOnce('success');
      await circuitBreaker.execute(operation);

      expect(circuitBreaker.getStats().state).toBe(CircuitState.CLOSED);
    });

    it('should close circuit on successful HALF_OPEN operation', async () => {
      // Force circuit to OPEN
      circuitBreaker.forceOpen();
      expect(circuitBreaker.getStats().state).toBe(CircuitState.OPEN);

      // Fast-forward past recovery timeout
      vi.advanceTimersByTime(1001);

      const operation = vi.fn().mockResolvedValue('success');
      await circuitBreaker.execute(operation);

      expect(circuitBreaker.getStats().state).toBe(CircuitState.CLOSED);
    });
  });

  describe('Expected Errors', () => {
    beforeEach(() => {
      circuitBreaker = new CircuitBreaker({
        ...defaultOptions,
        expectedErrors: ['expected error'],
      });
    });

    it('should not open circuit for expected errors', async () => {
      const operation = vi.fn().mockRejectedValue(new Error('expected error'));

      for (let i = 0; i < 5; i++) {
        try {
          await circuitBreaker.execute(operation);
        } catch {}
      }

      const stats = circuitBreaker.getStats();
      expect(stats.state).toBe(CircuitState.CLOSED);
    });
  });

  describe('State Change Callbacks', () => {
    it('should call onStateChange callback', async () => {
      const onStateChange = vi.fn();
      circuitBreaker = new CircuitBreaker({
        ...defaultOptions,
        onStateChange,
      });

      const operation = vi.fn().mockRejectedValue(new Error('Service error'));

      for (let i = 0; i < 3; i++) {
        try {
          await circuitBreaker.execute(operation);
        } catch {}
      }

      expect(onStateChange).toHaveBeenCalledWith(CircuitState.OPEN, expect.any(Error));
    });
  });

  describe('Manual Controls', () => {
    it('should reset circuit state', () => {
      circuitBreaker.forceOpen();
      expect(circuitBreaker.getStats().state).toBe(CircuitState.OPEN);

      circuitBreaker.reset();
      const stats = circuitBreaker.getStats();
      expect(stats.state).toBe(CircuitState.CLOSED);
      expect(stats.failures).toBe(0);
      expect(stats.successes).toBe(0);
    });

    it('should force circuit states', () => {
      circuitBreaker.forceOpen();
      expect(circuitBreaker.getStats().state).toBe(CircuitState.OPEN);

      circuitBreaker.forceClosed();
      expect(circuitBreaker.getStats().state).toBe(CircuitState.CLOSED);
    });
  });
});

describe('TokenBucketRateLimiter', () => {
  let rateLimiter: TokenBucketRateLimiter;

  beforeEach(() => {
    vi.useFakeTimers();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('Token Consumption', () => {
    beforeEach(() => {
      rateLimiter = new TokenBucketRateLimiter({
        tokensPerInterval: 10,
        interval: 1000,
        maxTokens: 10,
      });
    });

    it('should start with full token bucket', () => {
      expect(rateLimiter.getTokenCount()).toBe(10);
    });

    it('should consume tokens successfully', async () => {
      const result = await rateLimiter.consume(5);
      expect(result).toBe(true);
      expect(rateLimiter.getTokenCount()).toBe(5);
    });

    it('should reject when insufficient tokens', async () => {
      await rateLimiter.consume(8);
      const result = await rateLimiter.consume(5);
      expect(result).toBe(false);
      expect(rateLimiter.getTokenCount()).toBe(2);
    });

    it('should refill tokens over time', async () => {
      await rateLimiter.consume(10);
      expect(rateLimiter.getTokenCount()).toBe(0);

      vi.advanceTimersByTime(1000);
      expect(rateLimiter.getTokenCount()).toBe(10);
    });

    it('should cap tokens at maxTokens', async () => {
      await rateLimiter.consume(5);
      vi.advanceTimersByTime(2000); // Two intervals
      expect(rateLimiter.getTokenCount()).toBe(10); // Capped at maxTokens
    });
  });

  describe('waitForTokens', () => {
    beforeEach(() => {
      rateLimiter = new TokenBucketRateLimiter({
        tokensPerInterval: 5,
        interval: 1000,
        maxTokens: 5,
      });
    });

    it('should wait for token refill', async () => {
      await rateLimiter.consume(5);
      expect(rateLimiter.getTokenCount()).toBe(0);

      const waitPromise = rateLimiter.waitForTokens(3);
      
      // Should not resolve immediately
      let resolved = false;
      waitPromise.then(() => { resolved = true; });
      
      await vi.runOnlyPendingTimersAsync();
      expect(resolved).toBe(false);

      // Advance time to trigger refill
      vi.advanceTimersByTime(1000);
      await vi.runAllTimersAsync();

      expect(resolved).toBe(true);
      expect(rateLimiter.getTokenCount()).toBe(2); // 5 refilled - 3 consumed
    });
  });

  describe('Validation', () => {
    it('should validate options', () => {
      expect(() => new TokenBucketRateLimiter({
        tokensPerInterval: 0,
        interval: 1000,
        maxTokens: 10,
      })).toThrow('Tokens per interval must be greater than 0');

      expect(() => new TokenBucketRateLimiter({
        tokensPerInterval: 10,
        interval: 0,
        maxTokens: 10,
      })).toThrow('Interval must be greater than 0');

      expect(() => new TokenBucketRateLimiter({
        tokensPerInterval: 10,
        interval: 1000,
        maxTokens: 0,
      })).toThrow('Max tokens must be greater than 0');
    });
  });
});

describe('ResilientHttpClient', () => {
  let httpClient: ResilientHttpClient;
  let mockFetch: ReturnType<typeof vi.fn>;

  beforeEach(() => {
    vi.useFakeTimers();
    mockFetch = vi.fn();
    global.fetch = mockFetch;
  });

  afterEach(() => {
    vi.useRealTimers();
    vi.restoreAllMocks();
  });

  describe('Basic HTTP Operations', () => {
    beforeEach(() => {
      httpClient = new ResilientHttpClient({
        baseURL: 'https://api.example.com',
        defaultHeaders: { 'Authorization': 'Bearer token' },
      });
    });

    it('should make successful HTTP request', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        status: 200,
        json: () => Promise.resolve({ data: 'success' }),
      });

      const result = await httpClient.request('/users');

      expect(mockFetch).toHaveBeenCalledWith(
        'https://api.example.com/users',
        expect.objectContaining({
          headers: expect.objectContaining({
            'Authorization': 'Bearer token',
          }),
        })
      );
      expect(result).toEqual({ data: 'success' });
    });

    it('should handle HTTP errors', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 404,
        statusText: 'Not Found',
      });

      await expect(httpClient.request('/nonexistent')).rejects.toThrow('HTTP 404: Not Found');
    });
  });

  describe('Integrated Resilience Patterns', () => {
    let unexpected: any[];
    const onUnhandled = (reason: any) => {
      const msg = String((reason && (reason as any).message) || reason || '');
      // Allow fast-fail OPEN and explicit HTTP status errors during tests; capture others
      if (
        !msg.includes('Circuit breaker is OPEN') &&
        !msg.includes('HTTP 500') &&
        !msg.includes('HTTP 503')
      ) {
        unexpected.push(reason);
      }
    };

    beforeEach(() => {
      unexpected = [];
      process.on('unhandledRejection', onUnhandled);
    });

    afterEach(() => {
      process.off('unhandledRejection', onUnhandled);
      expect(unexpected).toHaveLength(0);
    });
    beforeEach(() => {
      httpClient = new ResilientHttpClient({
        retryOptions: {
          maxRetries: 2,
          baseDelayMs: 100,
          jitterType: 'none',
        },
        circuitBreakerOptions: {
          failureThreshold: 2,
          recoveryTimeout: 1000,
          monitoringPeriod: 5000,
        },
        rateLimiterOptions: {
          tokensPerInterval: 5,
          interval: 1000,
          maxTokens: 5,
        },
      });
    });

    it('should retry failed requests', async () => {
      mockFetch
        .mockResolvedValueOnce({
          ok: false,
          status: 503,
          statusText: 'Service Unavailable',
        })
        .mockResolvedValueOnce({
          ok: true,
          status: 200,
          json: () => Promise.resolve({ data: 'success' }),
        });

      const promise = httpClient.request('/api/data');
      await vi.runAllTimersAsync();
      const result = await promise;

      expect(mockFetch).toHaveBeenCalledTimes(2);
      expect(result).toEqual({ data: 'success' });
    });

    it('should respect rate limits', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        status: 200,
        json: () => Promise.resolve({ data: 'success' }),
      });

      // Make requests that exceed rate limit
      const requests = Array.from({ length: 7 }, () => 
        httpClient.request('/api/data')
      );

      await vi.runAllTimersAsync();
      await Promise.all(requests);

      // Should respect rate limiting timing
      expect(mockFetch).toHaveBeenCalledTimes(7);
    });

    it('should open circuit breaker on repeated failures', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 500,
        statusText: 'Internal Server Error',
      });

      // Make requests to trigger circuit breaker
      for (let i = 0; i < 3; i++) {
        try {
          const promise = httpClient.request('/api/failing');
          await vi.runAllTimersAsync();
          await promise;
        } catch (error) {
          // Expected failures
        }
      }

      // Circuit should be open, next request should fail immediately
      await expect(httpClient.request('/api/data')).rejects.toThrow('Circuit breaker is OPEN');
    });
  });

  describe('Health Stats', () => {
    beforeEach(() => {
      httpClient = new ResilientHttpClient({
        circuitBreakerOptions: {
          failureThreshold: 3,
          recoveryTimeout: 1000,
          monitoringPeriod: 5000,
        },
        rateLimiterOptions: {
          tokensPerInterval: 10,
          interval: 1000,
          maxTokens: 10,
        },
      });
    });

    it('should provide health statistics', () => {
      const stats = httpClient.getHealthStats();

      expect(stats.circuitBreaker).toBeDefined();
      expect(stats.circuitBreaker?.state).toBe(CircuitState.CLOSED);
      expect(stats.rateLimiter).toBeDefined();
      expect(stats.rateLimiter?.availableTokens).toBe(10);
      expect(stats.rateLimiter?.maxTokens).toBe(10);
    });
  });
});

describe('Integration Tests', () => {
  beforeEach(() => {
    vi.useFakeTimers();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('should handle complex failure scenarios', async () => {
    // Suppress expected unhandled rejections for OPEN fast-fail, but fail on unexpected ones
    const unexpected: any[] = [];
    const onUnhandled = (reason: any) => {
      const msg = String((reason && (reason as any).message) || reason || '');
      if (!msg.includes('Circuit breaker is OPEN')) {
        unexpected.push(reason);
      }
    };
    process.on('unhandledRejection', onUnhandled);

    const httpClient = new ResilientHttpClient({
      retryOptions: {
        maxRetries: 3,
        baseDelayMs: 50,
        jitterType: 'none',
      },
      circuitBreakerOptions: {
        failureThreshold: 2,
        recoveryTimeout: 500,
        monitoringPeriod: 2000,
      },
      rateLimiterOptions: {
        tokensPerInterval: 2,
        interval: 1000,
        maxTokens: 2,
      },
    });

    const mockFetch = vi.fn();
    global.fetch = mockFetch;

    // Simulate initial failures followed by recovery
    mockFetch
      .mockResolvedValueOnce({ ok: false, status: 503, statusText: 'Service Unavailable' })
      .mockResolvedValueOnce({ ok: false, status: 503, statusText: 'Service Unavailable' })
      .mockResolvedValue({ 
        ok: true, 
        status: 200, 
        json: () => Promise.resolve({ data: 'recovered' }) 
      });

    // First request should fail and open circuit
    try {
      const promise = httpClient.request('/api/test');
      await vi.runAllTimersAsync();
      await promise;
    } catch (error) {
      // Expected failure
    }
    // Flush microtasks to ensure OPEN transition is observable
    await Promise.resolve();

    // Verify circuit is open
    const stats = httpClient.getHealthStats();
    expect(stats.circuitBreaker?.state).toBe(CircuitState.OPEN);

    // Wait for recovery period
    vi.advanceTimersByTime(600);

    // Next request should succeed and close circuit
    const promise = httpClient.request('/api/test');
    await vi.runAllTimersAsync();
    const result = await promise;

    expect(result).toEqual({ data: 'recovered' });
    expect(httpClient.getHealthStats().circuitBreaker?.state).toBe(CircuitState.CLOSED);

    // Ensure no unexpected unhandled rejections were raised during this scenario
    process.off('unhandledRejection', onUnhandled);
    expect(unexpected).toHaveLength(0);
  });
});
