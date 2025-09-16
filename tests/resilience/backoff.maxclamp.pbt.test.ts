import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff none jitter clamps at maxDelay for large attempts', () => {
  it('once baseDelay(attempt) >= maxDelay, delay == maxDelay thereafter', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 200 }), mult: fc.integer({ min: 2, max: 5 }), pow: fc.integer({ min: 3, max: 8 }) }),
      async ({ base, mult, pow }) => {
        const maxDelayMs = base * Math.pow(mult, pow);
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'none' as const });
        let clamped = false;
        for (let attempt=0; attempt<=pow+2; attempt++) {
          const expected = Math.min(base * Math.pow(mult, attempt), maxDelayMs);
          const d = (s as any)['calculateDelay'](attempt);
          expect(d).toBe(expected);
          if (expected === maxDelayMs) {
            clamped = true;
          }
          if (clamped) {
            expect(d).toBe(maxDelayMs);
          }
        }
      }
    ), { numRuns: 30 });
  });
});
