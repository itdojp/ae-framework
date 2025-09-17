import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff decorrelated jitter long-run bounds', () => {
  it('attempts 1..8 stay within [base, min(max, 3*prevDet)]', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 100 }), mult: fc.integer({ min: 2, max: 5 }) }),
      async ({ base, mult }) => {
        const maxDelayMs = base * Math.pow(mult, 8);
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'decorrelated' as const });
        for (let attempt = 1; attempt <= 8; attempt++) {
          const d = (s as any)['calculateDelay'](attempt);
          const prevDet = Math.min(base * Math.pow(mult, Math.max(0, attempt - 1)), maxDelayMs);
          const minDelay = base;
          const maxDelay = Math.min(prevDet * 3, maxDelayMs);
          expect(d).toBeGreaterThanOrEqual(minDelay);
          expect(d).toBeLessThanOrEqual(maxDelay);
        }
      }
    ), { numRuns: 15 });
  });
});

