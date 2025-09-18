import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker reset timeout minimal recovery (fast)', () => {
  it('transitions OPEN -> HALF_OPEN -> CLOSED on successes after resetTimeout', async () => {
    const cb = new CircuitBreaker('cb-reset', {
      failureThreshold: 1,
      successThreshold: 2,
      halfOpenMaxCalls: 10,
      resetTimeoutMs: 5,
    } as any);

    // Force OPEN
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    // Wait to allow HALF_OPEN
    await new Promise(r => setTimeout(r, 6));
    // Provide enough successes to close
    await cb.execute(async () => 'ok');
    await cb.execute(async () => 'ok');
    // Should accept without throwing now
    await expect(cb.execute(async () => 'ok')).resolves.toBe('ok');
  });
});

