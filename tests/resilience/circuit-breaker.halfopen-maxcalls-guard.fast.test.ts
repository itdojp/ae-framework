import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker HALF_OPEN maxCalls guard (fast)', () => {
  it('limits number of attempts in HALF_OPEN (maxCalls=1)', async () => {
    const cb = new CircuitBreaker('cb-ho-max1', {
      failureThreshold: 1,
      successThreshold: 2,
      halfOpenMaxCalls: 1,
      resetTimeoutMs: 5,
    } as any);

    // Force OPEN
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();

    // Move to HALF_OPEN
    await new Promise(r => setTimeout(r, 6));

    // First attempt allowed (may succeed or fail)
    try { await cb.execute(async () => 'ok'); } catch {}

    // Second immediate attempt should be guarded when still HALF_OPEN and maxCalls=1
    let guarded = false;
    try { await cb.execute(async () => 'ok2'); } catch { guarded = true; }
    expect(guarded).toBe(true);
  });
});

