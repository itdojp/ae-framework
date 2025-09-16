import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff decorrelated jitter attempt=1 bounds', () => {
  it('delay lies within [base, min(maxDelay, 3*base)]', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 300 }), mult: fc.integer({ min: 2, max: 5 }) }),
      async ({ base, mult }) => {
        const maxDelayMs = base * mult * mult; // some headroom
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'decorrelated' as const });
        const d = (s as any)['calculateDelay'](1);
        const minDelay = base;
        const maxDelay = Math.min(maxDelayMs, base * 3);
        expect(d).toBeGreaterThanOrEqual(minDelay);
        expect(d).toBeLessThanOrEqual(maxDelay);
      }
    ), { numRuns: 20 });
  });
});
