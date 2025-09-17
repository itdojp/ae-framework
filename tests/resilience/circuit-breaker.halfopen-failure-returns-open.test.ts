import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker half-open failure returns to OPEN', () => {
  it('on half-open, a failure immediately forces OPEN and rejects subsequent calls until timeout', async () => {
    const timeout = 40;
    const cb = new CircuitBreaker('half-open-fail', {
      failureThreshold: 1,
      successThreshold: 1,
      timeout,
      monitoringWindow: 100,
    });

    // First call fails → OPEN
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);

    // Wait to become HALF_OPEN
    await new Promise(r => setTimeout(r, timeout + 5));
    // Next call fails in HALF_OPEN → immediately OPEN again
    await expect(cb.execute(async () => { throw new Error('fail-half'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);

    // During OPEN window, user calls are rejected
    await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(CircuitBreakerOpenError);
  });
});

