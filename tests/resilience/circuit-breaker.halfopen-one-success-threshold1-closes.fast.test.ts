import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker HALF_OPEN threshold=1 closes on first success (fast)', () => {
  it('moves to CLOSED after one success when successThreshold=1', async () => {
    const cb = new CircuitBreaker('cb-ho-th1-close', {
      failureThreshold: 1,
      successThreshold: 1,
      halfOpenMaxCalls: 5,
      resetTimeoutMs: 5,
    } as any);

    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    await new Promise(r => setTimeout(r, 6));

    await cb.execute(async () => 'ok');
    await expect(cb.execute(async () => 'ok2')).resolves.toBe('ok2');
  });
});

