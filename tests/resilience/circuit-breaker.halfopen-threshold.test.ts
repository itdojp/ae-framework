import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker HALF_OPEN success threshold boundary', () => {
  it('closes when successCount reaches successThreshold exactly', async () => {
    const cb = new CircuitBreaker('boundary', {
      failureThreshold: 1,
      successThreshold: 2,
      timeout: 10,
      monitoringWindow: 100,
    });
    // Open
    await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    // Wait to half-open
    await new Promise(r=>setTimeout(r, 12));
    // Two successes should close
    await cb.execute(async () => 1);
    expect(cb.getState()).toBe(CircuitState.HALF_OPEN);
    await cb.execute(async () => 2);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
  });
});

