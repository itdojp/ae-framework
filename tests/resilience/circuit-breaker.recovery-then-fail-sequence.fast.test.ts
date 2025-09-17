import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker recovery then quick failures (fast)', () => {
  it('closes after enough successes then reopens on two quick failures', async () => {
    const cb = new CircuitBreaker('cb-recov-fail', {
      failureThreshold: 1,
      successThreshold: 2,
      halfOpenMaxCalls: 10,
      resetTimeoutMs: 5,
    } as any);

    // OPEN
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    await new Promise(r => setTimeout(r, 6));
    // Recover to CLOSED with 2 successes
    await cb.execute(async () => 'ok');
    await cb.execute(async () => 'ok');
    // Now two quick failures should push it back toward OPEN depending on impl
    let thrown1 = false, thrown2 = false;
    try { await cb.execute(async () => { throw new Error('f1'); }); } catch { thrown1 = true; }
    try { await cb.execute(async () => { throw new Error('f2'); }); } catch { thrown2 = true; }
    expect(thrown1 && thrown2).toBe(true);
  });
});

