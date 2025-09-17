import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker failureThreshold=2 boundary', () => {
  it(
    // GWT-style title for consistency
    'Given failureThreshold=2 | When two consecutive failures | Then circuit opens (rejects until timeout)',
    async () => {
    const cb = new CircuitBreaker('fail2', {
      failureThreshold: 2,
      successThreshold: 1,
      timeout: 10,
      monitoringWindow: 100,
    });
    await expect(cb.execute(async () => { throw new Error('x1'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
    await expect(cb.execute(async () => { throw new Error('x2'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
  }
  );
});
