import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

describe('Resilience: CircuitBreaker transitions', () => {
  it('OPEN -> HALF_OPEN after timeout', async () => {
    const cb = new CircuitBreaker('transitions', {
      failureThreshold: 1,
      successThreshold: 1,
      timeout: 15, // ms
      monitoringWindow: 100,
    });
    // Force to OPEN by causing one failure
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeInstanceOf(Error);
    expect(cb.getState()).toBe(CircuitState.OPEN);
    // Wait beyond timeout to trigger HALF_OPEN schedule
    await new Promise((r) => setTimeout(r, 25));
    // Executing should be allowed in HALF_OPEN (not immediately rejecting)
    // and a success closes the breaker
    const result = await cb.execute(async () => 42);
    expect(result).toBe(42);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
  });
});

