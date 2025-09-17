import { describe, it, expect } from 'vitest';
import { CircuitBreaker } from '../../src/utils/circuit-breaker';

describe('CircuitBreaker HALF_OPEN two successes then allow (fast)', () => {
  it('closes after two successes and allows subsequent calls', async () => {
    const cb = new CircuitBreaker('cb-ho-2s-allow', {
      failureThreshold: 1,
      successThreshold: 2,
      halfOpenMaxCalls: 10,
      resetTimeoutMs: 5,
    } as any);

    // Force OPEN
    await expect(cb.execute(async () => { throw new Error('boom'); })).rejects.toBeTruthy();
    await new Promise(r => setTimeout(r, 6));

    // Two successes should transition to CLOSED
    await cb.execute(async () => 'ok1');
    await cb.execute(async () => 'ok2');

    // Now breaker should allow calls without throwing
    await expect(cb.execute(async () => 'ok3')).resolves.toBe('ok3');
  });
});

