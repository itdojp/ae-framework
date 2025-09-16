import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff decorrelated jitter near max boundary', () => {
  it('attempt ~= max exponent: base <= d <= min(maxDelay, 3*prevDet)', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 300 }), mult: fc.integer({ min: 2, max: 5 }), pow: fc.integer({ min: 3, max: 8 }) }),
      async ({ base, mult, pow }) => {
        const maxDelayMs = base * Math.pow(mult, pow);
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'decorrelated' as const });
        const attempt = pow; // near/at cap
        const d = (s as any)['calculateDelay'](attempt);
        const minDelay = base;
        const prevDet = Math.min(base * Math.pow(mult, Math.max(0, attempt - 1)), maxDelayMs);
        const maxDelay = Math.min(prevDet * 3, maxDelayMs);
        expect(d).toBeGreaterThanOrEqual(minDelay);
        expect(d).toBeLessThanOrEqual(maxDelay);
      }
    ), { numRuns: 30 });
  });
});

