import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { CircuitBreaker, CircuitState, CircuitBreakerOpenError } from '../../src/utils/circuit-breaker';

describe('PBT: CircuitBreaker basic invariants', () => {
  const mk = () => new CircuitBreaker('pbt', {
    failureThreshold: 3,
    successThreshold: 2,
    timeout: 10,
    monitoringWindow: 1000,
  });

  it('never goes to negative failure/success counts', async () => {
    await fc.assert(fc.asyncProperty(fc.array(fc.boolean(), { minLength: 1, maxLength: 50 }), async (arr) => {
      const cb = mk();
      for (const ok of arr) {
        if (ok) {
          try {
            await cb.execute(async () => 1);
          } catch (err) {
            expect(err).toBeInstanceOf(CircuitBreakerOpenError);
          }
        } else {
          try {
            await cb.execute(async () => { throw new Error('x'); });
          } catch (err) {
            if (err instanceof CircuitBreakerOpenError) {
              continue;
            }
            if (err instanceof Error && err.message === 'x') {
              // expected failure path
            } else {
              throw err;
            }
          }
        }
        const stats = cb.getStats();
        expect(stats.failureCount).toBeGreaterThanOrEqual(0);
        expect(stats.successCount).toBeGreaterThanOrEqual(0);
      }
    }), { numRuns: 50 });
  });

  it('OPEN state rejects execute unless half-open timeout reached', async () => {
    const cb = mk();
    // Force OPEN
    cb.forceOpen();
    expect(cb.getState()).toBe(CircuitState.OPEN);
    await expect(cb.execute(async () => 1)).rejects.toBeInstanceOf(CircuitBreakerOpenError);
  });
});
