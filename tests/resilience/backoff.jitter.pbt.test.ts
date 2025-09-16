import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff jitter bounds', () => {
  it('full jitter: 0 <= delay <= baseDelay(attempt)', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 1000 }) }),
      async ({ base }) => {
        const attempt = 1;
        const multiplier = 2;
        const maxDelayMs = base * 16;
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier, jitterType: 'full' as const });
        const expectedBaseDelay = Math.min(base * Math.pow(multiplier, attempt), maxDelayMs);
        const d = (s as any)['calculateDelay'](attempt);
        expect(d).toBeGreaterThanOrEqual(0);
        expect(d).toBeLessThanOrEqual(expectedBaseDelay);
      }
    ), { numRuns: 50 });
  });
  it('equal jitter: baseDelay/2 <= delay <= baseDelay(attempt)', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 2, max: 1000 }) }),
      async ({ base }) => {
        const attempt = 1;
        const multiplier = 2;
        const maxDelayMs = base * 16;
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier, jitterType: 'equal' as const });
        const expectedBaseDelay = Math.min(base * Math.pow(multiplier, attempt), maxDelayMs);
        const d = (s as any)['calculateDelay'](attempt);
        expect(d).toBeGreaterThanOrEqual(expectedBaseDelay / 2);
        expect(d).toBeLessThanOrEqual(expectedBaseDelay);
      }
    ), { numRuns: 50 });
  });
});
