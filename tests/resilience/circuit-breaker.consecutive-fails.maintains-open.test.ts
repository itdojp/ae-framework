import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker consecutive failures keep OPEN until timeout', () => {
  it('multiple calls during OPEN reject, state remains OPEN until half-open window', async () => {
    const timeout = 40;
    const cb = new CircuitBreaker('open-consecutive', {
      failureThreshold: 1,
      successThreshold: 1,
      timeout,
      monitoringWindow: 100,
    });
    await expect(cb.execute(async () => { throw new Error('f'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    for (let i=0; i<3; i++) {
      await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(CircuitBreakerOpenError);
      expect(cb.getState()).toBe(CircuitState.OPEN);
    }
    await new Promise(r => setTimeout(r, timeout + 5));
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
  });
});

