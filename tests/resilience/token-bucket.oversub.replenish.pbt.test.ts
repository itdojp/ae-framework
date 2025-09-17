import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket oversubscribe with replenish', () => {
  it(
    // GWT-style title for consistency
    'Given empty bucket | When waiting about one interval | Then tokens replenish (>0) and stay <= max',
    async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 10 }), interval: fc.integer({ min: 10, max: 60 }), max: fc.integer({ min: 5, max: 50 }) }),
      async ({ tokens, interval, max }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        await rl.consume(max); // drain
        const before = rl.getTokenCount();
        expect(before).toBeGreaterThanOrEqual(0);
        await new Promise(r => setTimeout(r, interval + 10));
        // small scheduler slack
        await new Promise(r => setTimeout(r, 5));
        const after = rl.getTokenCount();
        expect(after).toBeGreaterThanOrEqual(0);
        expect(after).toBeLessThanOrEqual(max);
      }
    ), { numRuns: 20 });
  }
  );
});
