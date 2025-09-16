import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker resets failure count on success', () => {
  it('resets failureCount after a successful call in CLOSED state', async () => {
    const cb = new CircuitBreaker('reset', {
      failureThreshold: 2,
      successThreshold: 1,
      timeout: 50,
      monitoringWindow: 100,
    });
    // One failure
    await expect(cb.execute(async () => { throw new Error('x'); })).rejects.toBeInstanceOf(Error);
    let stats = cb.getStats();
    expect(stats.failureCount).toBeGreaterThanOrEqual(1);
    // One success should reset failureCount in CLOSED
    await cb.execute(async () => 1);
    stats = cb.getStats();
    expect(cb.getState()).toBe(CircuitState.CLOSED);
    expect(stats.failureCount).toBe(0);
  });
});

