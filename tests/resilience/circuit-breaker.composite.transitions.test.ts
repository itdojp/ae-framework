import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker composite transitions', () => {
  it('CLOSED → OPEN (fail) → HALF_OPEN (timeout) → CLOSED (successThreshold) → OPEN (fail in CLOSED after threshold)', async () => {
    const timeout = 40;
    const cb = new CircuitBreaker('composite', {
      failureThreshold: 1,
      successThreshold: 1,
      timeout,
      monitoringWindow: 100,
    });

    // Initial failure opens circuit
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);

    // Wait until half-open window
    await new Promise(r => setTimeout(r, timeout + 5));
    // Success in HALF_OPEN closes circuit
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.CLOSED);

    // Subsequent failure in CLOSED opens circuit again
    await expect(cb.execute(async () => { throw new Error('again'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);

    // Calls during OPEN are rejected
    await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(CircuitBreakerOpenError);
  });
});

