import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff equal jitter sequence bounds', () => {
  it('for attempts 1..N: base/2 <= d_i <= base(attempt)', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 2, max: 400 }), mult: fc.integer({ min: 2, max: 4 }), steps: fc.integer({ min: 1, max: 8 }) }),
      async ({ base, mult, steps }) => {
        const maxDelayMs = base * Math.pow(mult, 6);
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'equal' as const });
        for (let attempt=1; attempt<=steps; attempt++) {
          const expectedBase = Math.min(base * Math.pow(mult, attempt), maxDelayMs);
          const d = (s as any)['calculateDelay'](attempt);
          expect(d).toBeGreaterThanOrEqual(expectedBase / 2);
          expect(d).toBeLessThanOrEqual(expectedBase);
        }
      }
    ), { numRuns: 30 });
  });
});

