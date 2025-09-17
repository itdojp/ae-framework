import { describe, it, expect } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import fc from 'fast-check';
import { BackoffStrategy } from '../../src/resilience/backoff-strategies';

describe('PBT: Backoff decorrelated jitter attempt=0 boundary', () => {
  it(formatGWT('decorrelated jitter', 'attempt=0', 'base <= delay <= min(maxDelay, 3*base)'), async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ base: fc.integer({ min: 1, max: 400 }), mult: fc.integer({ min: 2, max: 4 }) }),
      async ({ base, mult }) => {
        const maxDelayMs = base * Math.pow(mult, 6);
        const s = new BackoffStrategy({ baseDelayMs: base, maxDelayMs, multiplier: mult, jitterType: 'decorrelated' as const });
        const attempt = 0;
        const d = (s as any)['calculateDelay'](attempt);
        const minDelay = base;
        const maxDelay = Math.min(3 * base, maxDelayMs);
        expect(d).toBeGreaterThanOrEqual(minDelay);
        expect(d).toBeLessThanOrEqual(maxDelay);
      }
    ), { numRuns: 30 });
  });
});
