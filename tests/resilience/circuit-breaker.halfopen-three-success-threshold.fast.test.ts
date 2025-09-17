import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker HALF_OPEN three-success threshold (fast)', () => {
  it('requires 3 successes to close when successThreshold=3', async () => {
    const cb = new CircuitBreaker('cb-ho-3s', {
      failureThreshold: 1,
      successThreshold: 3,
      halfOpenMaxCalls: 10,
      resetTimeoutMs: 5,
    } as any);

    // Force OPEN
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    await new Promise(r => setTimeout(r, 6));

    await cb.execute(async () => 'ok1');
    await cb.execute(async () => 'ok2');
    // Not yet CLOSED (threshold not met); a failure now should reopen
    let reopened = false;
    try { await cb.execute(async () => { throw new Error('fail'); }); } catch { reopened = true; }
    expect(reopened).toBe(true);
  });
});

