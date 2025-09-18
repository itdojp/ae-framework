import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker HALF_OPEN maxCalls=2 guard (fast)', () => {
  it('allows two attempts, guards the third while HALF_OPEN', async () => {
    const cb = new CircuitBreaker('cb-ho-max2', {
      failureThreshold: 1,
      successThreshold: 3,
      halfOpenMaxCalls: 2,
      resetTimeoutMs: 5,
    } as any);

    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    await new Promise(r => setTimeout(r, 6));

    // Two attempts allowed
    try { await cb.execute(async () => 'ok1'); } catch {}
    try { await cb.execute(async () => 'ok2'); } catch {}

    // Third attempt in HALF_OPEN should be guarded
    let guarded = false;
    try { await cb.execute(async () => 'ok3'); } catch { guarded = true; }
    expect(guarded).toBe(true);
  });
});

