import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker stays OPEN until timeout elapses', () => {
  it('rejects during OPEN window and transitions to HALF_OPEN after timeout', async () => {
    const timeout = 40;
    const cb = new CircuitBreaker('open-stays', {
      failureThreshold: 1,
      successThreshold: 1,
      timeout,
      monitoringWindow: 100,
    });
    await expect(cb.execute(async () => { throw new Error('f'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    // Immediately try again: must reject
    await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(CircuitBreakerOpenError);
    // After timeout: allow trial (HALF_OPEN)
    await new Promise(r => setTimeout(r, timeout + 5));
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
  });
});

