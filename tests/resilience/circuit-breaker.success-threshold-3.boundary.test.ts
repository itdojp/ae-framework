import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker successThreshold=3 boundary', () => {
  it('requires 3 consecutive successes in HALF_OPEN to close', async () => {
    const cb = new CircuitBreaker('succ3', {
      failureThreshold: 1,
      successThreshold: 3,
      timeout: 10,
      monitoringWindow: 100,
    });
    // Open
    await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    // Go HALF_OPEN
    await new Promise(r => setTimeout(r, 12));
    // 1st success -> remain HALF_OPEN
    await cb.execute(async () => 1);
    expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
    // 2nd success -> remain HALF_OPEN
    await cb.execute(async () => 1);
    expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
    // 3rd success -> CLOSED
    await cb.execute(async () => 1);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
  });
});

