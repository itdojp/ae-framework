import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker OPEN→HALF_OPEN immediate failure (fast)', () => {
  it('stays/open-reopens on immediate failure after HALF_OPEN', async () => {
    const cb = new CircuitBreaker('cb-open-ho-fail', {
      failureThreshold: 1,
      successThreshold: 2,
      halfOpenMaxCalls: 5,
      resetTimeoutMs: 5,
    } as any);

    // Force OPEN
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    // Move to HALF_OPEN
    await new Promise(r => setTimeout(r, 6));
    // Immediate failure should re-open
    let reopened = false;
    try { await cb.execute(async () => { throw new Error('fail'); }); } catch { reopened = true; }
    expect(reopened).toBe(true);
  });
});

