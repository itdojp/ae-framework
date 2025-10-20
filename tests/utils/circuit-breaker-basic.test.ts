import { describe, test, expect, beforeEach, afterEach, vi } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker.js';

describe('CircuitBreaker - Basic Functionality', () => {
  let circuitBreaker: CircuitBreaker;

  beforeEach(() => {
    vi.useFakeTimers();
    circuitBreaker = new CircuitBreaker('test-breaker', {
      failureThreshold: 3,
      successThreshold: 2,
      timeout: 1000,
      monitoringWindow: 60000,
      enableMonitoring: true
    });
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  test(formatGWT('new breaker', 'constructed', 'starts in CLOSED'), () => {
    expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
  });

  test(formatGWT('operation succeeds', 'execute', 'remains CLOSED'), async () => {
    const result = await circuitBreaker.execute(async () => {
      return 'success';
    });
    
    expect(result).toBe('success');
    expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
  });

  test('should handle single failure', async () => {
    try {
      await circuitBreaker.execute(async () => {
        throw new Error('Test failure');
      });
    } catch (error) {
      expect(error.message).toBe('Test failure');
    }
    
    expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
  });

  test('should open circuit after reaching failure threshold', async () => {
    // Generate 3 failures to reach threshold
    for (let i = 0; i < 3; i++) {
      try {
        await circuitBreaker.execute(async () => {
          throw new Error(`Failure ${i + 1}`);
        });
      } catch (error) {
        // Expected to fail
      }
    }
    
    expect(circuitBreaker.getState()).toBe(CircuitState.OPEN);
  });

  test('should reject requests when circuit is OPEN', async () => {
    // First, open the circuit
    for (let i = 0; i < 3; i++) {
      try {
        await circuitBreaker.execute(async () => {
          throw new Error(`Failure ${i + 1}`);
        });
      } catch (error) {
        // Expected to fail
      }
    }
    
    expect(circuitBreaker.getState()).toBe(CircuitState.OPEN);
    
    // Now try to execute - should be rejected immediately
    try {
      await circuitBreaker.execute(async () => {
        return 'should not execute';
      });
      expect.fail('Should have thrown CircuitBreakerOpenError');
    } catch (error) {
      expect(error.name).toBe('CircuitBreakerOpenError');
    }
  });

  test('should transition to HALF_OPEN after timeout', async () => {
    // Create circuit breaker with very short timeout
    const shortTimeoutBreaker = new CircuitBreaker('short-timeout-breaker', {
      failureThreshold: 2,
      successThreshold: 1,
      timeout: 50, // 50ms timeout
      monitoringWindow: 60000
    });
    
    // Open the circuit
    for (let i = 0; i < 2; i++) {
      try {
        await shortTimeoutBreaker.execute(async () => {
          throw new Error(`Failure ${i + 1}`);
        });
      } catch (error) {
        // Expected to fail
      }
    }
    
    expect(shortTimeoutBreaker.getState()).toBe(CircuitState.OPEN);
    
    // Wait for timeout using fake timers
    vi.advanceTimersByTime(100);
    await Promise.resolve(); // allow any pending microtasks to run
    
    // Next call should transition to HALF_OPEN
    try {
      await shortTimeoutBreaker.execute(async () => {
        return 'test';
      });
    } catch (error) {
      // May fail, but state should be HALF_OPEN or CLOSED
    }
    
    // Should not be OPEN anymore
    expect(shortTimeoutBreaker.getState()).not.toBe(CircuitState.OPEN);
  });

  test('should reset circuit breaker', async () => {
    // Open the circuit first
    for (let i = 0; i < 3; i++) {
      try {
        await circuitBreaker.execute(async () => {
          throw new Error(`Failure ${i + 1}`);
        });
      } catch (error) {
        // Expected to fail
      }
    }
    
    // Reset should close the circuit
    circuitBreaker.reset();
    expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
  });

  test('should provide statistics', async () => {
    // Execute some operations
    try {
      await circuitBreaker.execute(async () => 'success1');
      await circuitBreaker.execute(async () => 'success2');
      await circuitBreaker.execute(async () => { throw new Error('failure1'); });
    } catch (error) {
      // Expected to fail on last operation
    }
    
    const stats = circuitBreaker.getStats();
    
    expect(stats.totalRequests).toBe(3);
    expect(stats.totalSuccesses).toBe(2);
    expect(stats.totalFailures).toBe(1);
    expect(stats.state).toBe(CircuitState.CLOSED);
  });

  test('should check circuit health through state', async () => {
    expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED); // Healthy
    
    // Open the circuit
    for (let i = 0; i < 3; i++) {
      try {
        await circuitBreaker.execute(async () => {
          throw new Error(`Failure ${i + 1}`);
        });
      } catch (error) {
        // Expected to fail
      }
    }
    
    expect(circuitBreaker.getState()).toBe(CircuitState.OPEN); // Unhealthy
  });

  test('should handle async operations correctly', async () => {
    const result = await circuitBreaker.execute(async () => {
      // Use fake timer for async operation
      const asyncPromise = new Promise(resolve => {
        setTimeout(() => resolve('async-success'), 10);
      });
      vi.advanceTimersByTime(10);
      return await asyncPromise;
    });
    
    expect(result).toBe('async-success');
  });

  test('should measure response time', async () => {
    await circuitBreaker.execute(async () => {
      // Simulate 50ms delay with fake timers
      const delayPromise = new Promise(resolve => setTimeout(resolve, 50));
      vi.advanceTimersByTime(50);
      await delayPromise;
      return 'delayed-success';
    });
    
    const stats = circuitBreaker.getStats();
    expect(stats.averageResponseTime).toBeGreaterThan(40); // Should be around 50ms
  });

  test('should force circuit states', () => {
    expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
    
    circuitBreaker.forceOpen();
    expect(circuitBreaker.getState()).toBe(CircuitState.OPEN);
    
    circuitBreaker.forceClose();
    expect(circuitBreaker.getState()).toBe(CircuitState.CLOSED);
  });
});
