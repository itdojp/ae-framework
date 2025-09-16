import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

class ExpectedErr extends Error {}
class UnexpectedErr extends Error {}

describe('Resilience: CircuitBreaker expectedErrors behavior', () => {
  it('counts only expectedErrors towards opening the circuit', async () => {
    const cb = new CircuitBreaker('expected', {
      failureThreshold: 1,
      successThreshold: 1,
      timeout: 10,
      monitoringWindow: 100,
      expectedErrors: [ExpectedErr],
    });
    // Unexpected error should not open the circuit
    await expect(cb.execute(async () => { throw new UnexpectedErr('u'); })).rejects.toBeInstanceOf(UnexpectedErr);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
    // Expected error should open the circuit
    await expect(cb.execute(async () => { throw new ExpectedErr('e'); })).rejects.toBeInstanceOf(ExpectedErr);
    expect(cb.getState()).toBe(CircuitState.OPEN);
  });
});

