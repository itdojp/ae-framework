import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket oversubscription safety', () => {
  it('excessive consume returns false and tokens stay non-negative', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 50 }), interval: fc.integer({ min: 1, max: 50 }), max: fc.integer({ min: 1, max: 100 }), req: fc.integer({ min: 1, max: 150 }) }),
      async ({ tokens, interval, max, req }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        const ok = await rl.consume(req);
        const count = rl.getTokenCount();
        if (req > max) expect(ok).toBe(false);
        expect(count).toBeGreaterThanOrEqual(0);
        expect(count).toBeLessThanOrEqual(max);
      }
    ), { numRuns: 40 });
  });
});
