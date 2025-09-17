import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker HALF_OPEN failure then enough successes (fast)', () => {
  it('fails once in HALF_OPEN then closes after reaching threshold', async () => {
    const cb = new CircuitBreaker('cb-ho-f-then-close', {
      failureThreshold: 1,
      successThreshold: 2,
      halfOpenMaxCalls: 10,
      resetTimeoutMs: 5,
    } as any);

    // Force OPEN
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    await new Promise(r => setTimeout(r, 6));

    // First call in HALF_OPEN fails
    let failed = false;
    try { await cb.execute(async () => { throw new Error('f1'); }); } catch { failed = true; }
    expect(failed).toBe(true);

    // Wait and then provide enough successes to close
    await new Promise(r => setTimeout(r, 6));
    await cb.execute(async () => 'ok1');
    await cb.execute(async () => 'ok2');
    // Should be CLOSED: next call succeeds
    await expect(cb.execute(async () => 'ok3')).resolves.toBe('ok3');
  });
});

