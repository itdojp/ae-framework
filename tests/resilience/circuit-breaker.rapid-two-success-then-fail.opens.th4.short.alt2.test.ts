import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/resilience/backoff-strategies';

describe('CircuitBreaker rapid (th=4) — two successes then a failure opens (alt2)', () => {
  it('remains CLOSED on two successes, then OPENs on failure', async () => {
    const cb = new CircuitBreaker({
      failureThreshold: 2,
      successThreshold: 4,
      recoveryTimeout: 10,
      monitoringPeriod: 50,
    });
    await cb.execute(async () => true);
    expect(cb.getStats().state).toBe(CircuitState.CLOSED);
    await cb.execute(async () => true);
    expect(cb.getStats().state).toBe(CircuitState.CLOSED);
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toThrow('boom');
    expect(cb.getStats().state).toBe(CircuitState.OPEN);
  });
});

