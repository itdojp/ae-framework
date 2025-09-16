import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker OPEN error message contract', () => {
  it('should include "Circuit breaker \u0027{name}\u0027 is OPEN" when rejecting calls', async () => {
    const name = 'open-msg';
    const cb = new CircuitBreaker(name, {
      failureThreshold: 1,
      successThreshold: 1,
      timeout: 50,
      monitoringWindow: 100,
    });
    // Force open by failing once
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);

    // Next call should synchronously reject with CircuitBreakerOpenError and message contract
    await expect(cb.execute(async () => 42)).rejects.toSatisfy((e: unknown) => {
      const err = e as Error;
      return err instanceof CircuitBreakerOpenError && /Circuit breaker 'open-msg' is OPEN/.test(err.message);
    });
  });
});

