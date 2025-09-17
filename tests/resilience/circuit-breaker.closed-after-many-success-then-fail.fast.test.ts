import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker CLOSED after many successes then single failure (fast)', () => {
  it('reopens on failure after being CLOSED with prior successes (th=1)', async () => {
    const cb = new CircuitBreaker('cb-closed-many-then-fail', {
      failureThreshold: 1,
      successThreshold: 2,
      halfOpenMaxCalls: 10,
      resetTimeoutMs: 5,
    } as any);

    // Move to CLOSED via OPEN -> HALF_OPEN -> successes
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    await new Promise(r => setTimeout(r, 6));
    await cb.execute(async () => 'ok1');
    await cb.execute(async () => 'ok2');
    await cb.execute(async () => 'ok3');

    // Now a single failure should reopen (threshold=1)
    let reopened = false;
    try { await cb.execute(async () => { throw new Error('fail'); }); } catch { reopened = true; }
    expect(reopened).toBe(true);
  });
});

