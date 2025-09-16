import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff decorrelated jitter sequence bounds', () => {
  it('for attempts 1..N: min<=d_i<=min(maxDelay,3*d_{i-1})', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 500 }), mult: fc.integer({ min: 2, max: 4 }), steps: fc.integer({ min: 2, max: 8 }) }),
      async ({ base, mult, steps }) => {
        const maxDelayMs = base * Math.pow(mult, 6);
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'decorrelated' as const });
        for (let attempt=1; attempt<=steps; attempt++) {
          const d = (s as any)['calculateDelay'](attempt);
          const minDelay = base;
          const prevDet = Math.min(base * Math.pow(mult, Math.max(0, attempt - 1)), maxDelayMs);
          const maxDelay = Math.min(prevDet * 3, maxDelayMs);
          expect(d).toBeGreaterThanOrEqual(minDelay);
          expect(d).toBeLessThanOrEqual(maxDelay);
        }
      }
    ), { numRuns: 30 });
  });
});
