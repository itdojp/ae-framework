import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff full jitter bounds across attempts', () => {
  it('full jitter: 0 <= delay <= base(attempt) for attempts 0..6', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 500 }), mult: fc.integer({ min: 1, max: 4 }) }),
      async ({ base, mult }) => {
        const maxDelayMs = base * Math.pow(mult, 6);
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'full' as const });
        for (let attempt=0; attempt<=6; attempt++) {
          const expectedBase = Math.min(base * Math.pow(mult, attempt), maxDelayMs);
          const d = (s as any)['calculateDelay'](attempt);
          expect(d).toBeGreaterThanOrEqual(0);
          expect(d).toBeLessThanOrEqual(expectedBase);
        }
      }
    ), { numRuns: 30 });
  });
});
