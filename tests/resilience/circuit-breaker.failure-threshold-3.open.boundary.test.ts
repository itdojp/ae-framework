import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker failureThreshold=3 boundary', () => {
  it('opens after three consecutive failures and rejects until half-open window', async () => {
    const timeout = 40;
    const cb = new CircuitBreaker('fail3', {
      failureThreshold: 3,
      successThreshold: 1,
      timeout,
      monitoringWindow: 100,
    });
    await expect(cb.execute(async () => { throw new Error('f1'); })).rejects.toBeInstanceOf(Error);
    await expect(cb.execute(async () => { throw new Error('f2'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
    await expect(cb.execute(async () => { throw new Error('f3'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(CircuitBreakerOpenError);
    await new Promise(r => setTimeout(r, timeout + 5));
    await expect(cb.execute(async () => 1)).resolves.toBe(1);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
  });
});

