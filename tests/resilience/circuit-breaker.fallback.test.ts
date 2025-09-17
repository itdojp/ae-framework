import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';
import { formatGWT } from '../utils/gwt-format';

describe('Resilience: CircuitBreaker fallback behavior', () => {
  it(
    formatGWT('OPEN state', 'execute with configured fallback', 'returns fallback value without throwing'),
    async () => {
    const cb = new CircuitBreaker('fallback', {
      failureThreshold: 1,
      successThreshold: 1,
      timeout: 1000,
      monitoringWindow: 100,
      fallback: () => 99,
    });
    // Open the circuit by failing once
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    // With fallback defined, execute should not throw, but return fallback value
    const val = await cb.execute(async () => 1).catch((e) => {
      // Should not reach here with fallback
      if (e instanceof CircuitBreakerOpenError) return -1;
      throw e;
    });
    expect(val).toBe(99);
  }
  );
});
