import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff jitter (decorrelated/none)', () => {
  it('decorrelated jitter: minDelay <= delay <= min(maxDelay, 3*prevDelay)', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 1000 }), mult: fc.integer({ min: 2, max: 4 }), attempt: fc.integer({ min: 1, max: 6 }) }),
      async ({ base, mult, attempt }) => {
        const maxDelayMs = base * Math.pow(mult, 6);
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'decorrelated' as const });
        const prevDelay = Math.min(base * Math.pow(mult, Math.max(0, attempt - 1)), maxDelayMs);
        const minDelay = base;
        const maxDelay = Math.min(prevDelay * 3, maxDelayMs);
        const d = (s as any)['calculateDelay'](attempt);
        expect(d).toBeGreaterThanOrEqual(minDelay);
        expect(d).toBeLessThanOrEqual(maxDelay);
      }
    ), { numRuns: 50 });
  });

  it('none jitter: delay == baseDelay(attempt)', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 1000 }), mult: fc.integer({ min: 1, max: 4 }), attempt: fc.integer({ min: 0, max: 6 }) }),
      async ({ base, mult, attempt }) => {
        const maxDelayMs = base * Math.pow(mult, 6);
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'none' as const });
        const expected = Math.min(base * Math.pow(mult, attempt), maxDelayMs);
        const d = (s as any)['calculateDelay'](attempt);
        expect(d).toBe(expected);
      }
    ), { numRuns: 50 });
  });
});

