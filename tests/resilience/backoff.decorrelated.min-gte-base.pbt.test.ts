import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Decorrelated jitter min delay >= base', () => {
  it('for attempts 1..10, delay >= base and <= min(max, 3*prevDet)', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 200 }), mult: fc.integer({ min: 2, max: 5 }) }),
      async ({ base, mult }) => {
        const maxDelayMs = base * Math.pow(mult, 10);
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'decorrelated' as const });
        for (let attempt=1; attempt<=10; attempt++){
          const d = (s as any)['calculateDelay'](attempt);
          const prevDet = Math.min(base * Math.pow(mult, Math.max(0, attempt-1)), maxDelayMs);
          expect(d).toBeGreaterThanOrEqual(base);
          expect(d).toBeLessThanOrEqual(Math.min(prevDet*3, maxDelayMs));
        }
      }
    ), { numRuns: 10 });
  });
});

