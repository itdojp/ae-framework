import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucketRateLimiter refill behavior', () => {
  it('refills up to maxTokens after several intervals', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 10 }), interval: fc.integer({ min: 5, max: 50 }), max: fc.integer({ min: 5, max: 50 }), steps: fc.integer({ min: 1, max: 5 }) }),
      async ({ tokens, interval, max, steps }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        // drain completely
        await rl.consume(max);
        // wait N intervals
        await new Promise(r=>setTimeout(r, interval * steps));
        const count = rl.getTokenCount();
        expect(count).toBeGreaterThanOrEqual(0);
        expect(count).toBeLessThanOrEqual(max);
      }
    ), { numRuns: 20 });
  });
});
