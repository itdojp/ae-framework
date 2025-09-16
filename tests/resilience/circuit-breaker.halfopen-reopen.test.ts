import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker HALF_OPEN failure reopens', () => {
  it('any failure in HALF_OPEN transitions back to OPEN', async () => {
    const cb = new CircuitBreaker('halfopen', {
      failureThreshold: 1,
      successThreshold: 2,
      timeout: 10,
      monitoringWindow: 100,
    });
    // Open first
    await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    // Wait for half-open window
    await new Promise((r) => setTimeout(r, 15));
    // In HALF_OPEN, a failure should go back to OPEN
    await expect(cb.execute(async () => { throw new Error('fail2'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
  });
});

