import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker half-open quick reopen (fast)', () => {
  it('reopens on failure after initial success in HALF_OPEN', async () => {
    const cb = new CircuitBreaker('cb-quick-reopen', {
      failureThreshold: 1,
      successThreshold: 3,
      halfOpenMaxCalls: 10,
      resetTimeoutMs: 5,
    } as any);

    // To OPEN
    await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeTruthy();
    await new Promise(r => setTimeout(r, 6));
    // First success in HALF_OPEN
    await expect(cb.execute(async () => 'ok')).resolves.toBe('ok');
    // Then a failure should reopen
    let reopened = false;
    try {
      await cb.execute(async () => { throw new Error('boom'); });
    } catch {
      reopened = true;
    }
    expect(reopened).toBe(true);
  });
});

