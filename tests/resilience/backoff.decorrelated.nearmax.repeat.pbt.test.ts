import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff decorrelated jitter near-max repeated bounds', () => {
  it('around near-max, repeated attempts stay within [base, min(max, 3*prevDet)]', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({ base: fc.integer({ min: 1, max: 200 }), mult: fc.integer({ min: 2, max: 4 }) }),
        async ({ base, mult }) => {
          const maxDelayMs = base * Math.pow(mult, 6);
          const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'decorrelated' as const });
          // probe attempts near the cap
          for (let attempt = 4; attempt <= 6; attempt++) {
            for (let rep = 0; rep < 2; rep++) {
              const d = (s as any)['calculateDelay'](attempt);
              const prevDet = Math.min(base * Math.pow(mult, Math.max(0, attempt - 1)), maxDelayMs);
              const minDelay = base;
              const maxDelay = Math.min(prevDet * 3, maxDelayMs);
              expect(d).toBeGreaterThanOrEqual(minDelay);
              expect(d).toBeLessThanOrEqual(maxDelay);
            }
          }
        }
      ),
      { numRuns: 15 }
    );
  });
});

