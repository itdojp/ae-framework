import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/utils/circuit-breaker';

class ExpectedA extends Error {}
class ExpectedB extends Error {}
class UnexpectedC extends Error {}

describe('Resilience: CircuitBreaker expectedErrors with multiple types', () => {
  it('counts only expected error classes towards opening', async () => {
    const cb = new CircuitBreaker('multi-expected', {
      failureThreshold: 2,
      successThreshold: 1,
      timeout: 10,
      monitoringWindow: 100,
      expectedErrors: [ExpectedA, ExpectedB],
    });
    // Unexpected should not count
    await expect(cb.execute(async () => { throw new UnexpectedC('u'); })).rejects.toBeInstanceOf(UnexpectedC);
    expect(cb.getState()).toBe(CircuitState.CLOSED);
    // Two expected errors open
    await expect(cb.execute(async () => { throw new ExpectedA('a'); })).rejects.toBeInstanceOf(ExpectedA);
    await expect(cb.execute(async () => { throw new ExpectedB('b'); })).rejects.toBeInstanceOf(ExpectedB);
    expect(cb.getState()).toBe(CircuitState.OPEN);
  });
});

