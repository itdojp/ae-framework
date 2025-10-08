import { describe, it, expect } from 'vitest';
import { CircuitBreaker, CircuitState } from '../../src/resilience/backoff-strategies';

describe('CircuitBreaker rapid (th=5) — five successes then a failure opens (short alt2)', () => {
  it('stays CLOSED on successes then OPENs on a failure', async () => {
    const cb = new CircuitBreaker({
      failureThreshold: 3,
      successThreshold: 5,
      recoveryTimeout: 10,
      monitoringPeriod: 50,
    });

    for (let i = 0; i < 5; i++) {
      await cb.execute(async () => true);
      expect(cb.getStats().state).toBe(CircuitState.CLOSED);
    }
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toThrow('boom');
    expect(cb.getStats().state).toBe(CircuitState.CLOSED);
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toThrow('boom');
    expect(cb.getStats().state).toBe(CircuitState.CLOSED);
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toThrow('boom');
    expect(cb.getStats().state).toBe(CircuitState.OPEN);
  });
});

