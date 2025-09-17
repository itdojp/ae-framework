import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff decorrelated jitter middle attempts', () => {
  it('attempt in 2..6 has bounded delay [base, min(max, 3*prevDet)]', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 200 }), mult: fc.integer({ min: 2, max: 5 }), attempt: fc.integer({ min: 2, max: 6 }) }),
      async ({ base, mult, attempt }) => {
        const maxDelayMs = base * Math.pow(mult, 8); // ample headroom
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'decorrelated' as const });
        const d = (s as any)['calculateDelay'](attempt);
        const minDelay = base;
        const prevDet = Math.min(base * Math.pow(mult, Math.max(0, attempt - 1)), maxDelayMs);
        const maxDelay = Math.min(prevDet * 3, maxDelayMs);
        expect(d).toBeGreaterThanOrEqual(minDelay);
        expect(d).toBeLessThanOrEqual(maxDelay);
      }
    ), { numRuns: 20 });
  });
});

