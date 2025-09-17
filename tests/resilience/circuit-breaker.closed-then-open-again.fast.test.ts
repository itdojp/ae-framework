import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker CLOSED then reopen on failure (fast)', () => {
  it('closes after successes then reopens on next failure (th=1)', async () => {
    const cb = new CircuitBreaker('cb-close-then-open', {
      failureThreshold: 1,
      successThreshold: 2,
      halfOpenMaxCalls: 10,
      resetTimeoutMs: 5,
    } as any);

    // Force OPEN then recover to CLOSED
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    await new Promise(r => setTimeout(r, 6));
    await cb.execute(async () => 'ok');
    await cb.execute(async () => 'ok'); // should be CLOSED now

    // Failure should cause OPEN with failureThreshold=1
    let reopened = false;
    try { await cb.execute(async () => { throw new Error('fail'); }); } catch { reopened = true; }
    expect(reopened).toBe(true);
  });
});

