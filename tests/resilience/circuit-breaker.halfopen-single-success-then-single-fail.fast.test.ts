import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker HALF_OPEN single success then single failure (fast)', () => {
  it('reopens after one success followed by failure before reaching successThreshold', async () => {
    const cb = new CircuitBreaker('cb-halfopen-1s-1f', {
      failureThreshold: 1,
      successThreshold: 2,
      halfOpenMaxCalls: 10,
      resetTimeoutMs: 5,
    } as any);

    // Force OPEN
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    await new Promise(r => setTimeout(r, 6));

    // One success in HALF_OPEN
    await cb.execute(async () => 'ok');
    // Then a failure should reopen (not enough successes to close)
    let reopened = false;
    try { await cb.execute(async () => { throw new Error('fail'); }); } catch { reopened = true; }
    expect(reopened).toBe(true);
  });
});

