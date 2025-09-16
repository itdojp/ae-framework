import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff near maxDelay bounds (equal/full)', () => {
  it('equal/full jitter stay within [low, base(attempt)] near max', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 2, max: 200 }), mult: fc.integer({ min: 2, max: 5 }), pow: fc.integer({ min: 3, max: 8 }) }),
      async ({ base, mult, pow }) => {
        const maxDelayMs = base * Math.pow(mult, pow);
        const expected = (attempt: number) => Math.min(base * Math.pow(mult, attempt), maxDelayMs);
        const eq = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'equal' as const });
        const fu = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'full' as const });
        const attempt = pow; // boundary at or near max
        const dEq = (eq as any)['calculateDelay'](attempt);
        const dFu = (fu as any)['calculateDelay'](attempt);
        const baseDelay = expected(attempt);
        expect(dEq).toBeGreaterThanOrEqual(baseDelay / 2);
        expect(dEq).toBeLessThanOrEqual(baseDelay);
        expect(dFu).toBeGreaterThanOrEqual(0);
        expect(dFu).toBeLessThanOrEqual(baseDelay);
      }
    ), { numRuns: 30 });
  });
});

