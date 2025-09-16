import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff boundaries and monotonicity', () => {
  it('none jitter: delays are non-decreasing and clamp at maxDelay', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          base: fc.integer({ min: 1, max: 500 }),
          mult: fc.integer({ min: 1, max: 4 }),
          maxPow: fc.integer({ min: 4, max: 8 })
        }),
        async ({ base, mult, maxPow }) => {
          const maxDelayMs = base * Math.pow(mult, maxPow);
          const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'none' as const });
          const delays: number[] = [];
          for (let attempt=0; attempt<=maxPow+2; attempt++) {
            const d = (s as any)['calculateDelay'](attempt);
            delays.push(d);
          }
          // Non-decreasing
          for (let i=1;i<delays.length;i++) {
            expect(delays[i]).toBeGreaterThanOrEqual(delays[i-1]);
          }
          // Eventually clamped to maxDelay
          expect(delays[delays.length-1]).toBe(maxDelayMs);
        }
      ),
      { numRuns: 50 }
    );
  });

  it('attempt=0 boundaries (full/equal/none)', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({ base: fc.integer({ min: 1, max: 1000 }), mult: fc.integer({ min: 1, max: 4 }) }),
        async ({ base, mult }) => {
          const maxDelayMs = base * Math.pow(mult, 6);
          const expected = Math.min(base * Math.pow(mult, 0), maxDelayMs);

          const sNone = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'none' as const });
          const dNone = (sNone as any)['calculateDelay'](0);
          expect(dNone).toBe(expected);

          const sEqual = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'equal' as const });
          const dEqual = (sEqual as any)['calculateDelay'](0);
          expect(dEqual).toBeGreaterThanOrEqual(expected / 2);
          expect(dEqual).toBeLessThanOrEqual(expected);

          const sFull = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'full' as const });
          const dFull = (sFull as any)['calculateDelay'](0);
          expect(dFull).toBeGreaterThanOrEqual(0);
          expect(dFull).toBeLessThanOrEqual(expected);
        }
      ),
      { numRuns: 50 }
    );
  });
});

