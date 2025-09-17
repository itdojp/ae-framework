import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker HALF_OPEN success threshold +1 (fast)', () => {
  it('re-opens when failure occurs after threshold-1 successes', async () => {
    const cb = new CircuitBreaker('test-cb', {
      failureThreshold: 1,
      successThreshold: 3,
      halfOpenMaxCalls: 10,
      resetTimeoutMs: 5,
    } as any);

    // Force OPEN
    await expect(cb.execute(async () => { throw new Error('fail'); })).rejects.toBeTruthy();

    // Wait then transition to HALF_OPEN
    await new Promise(r => setTimeout(r, 6));

    // Two successes (< threshold)
    await cb.execute(async () => 'ok');
    await cb.execute(async () => 'ok');

    // Then a failure triggers OPEN again (threshold+1 boundary guard)
    await expect(cb.execute(async () => { throw new Error('fail2'); })).rejects.toBeTruthy();
  });
});

