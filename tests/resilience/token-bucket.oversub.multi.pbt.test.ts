import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket oversubscription multi-step safety', () => {
  it('repeated oversubscribe never goes negative and stays bounded', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 10 }), interval: fc.integer({ min: 5, max: 50 }), max: fc.integer({ min: 5, max: 50 }), steps: fc.integer({ min: 2, max: 6 }) }),
      async ({ tokens, interval, max, steps }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        // drain
        await rl.consume(max);
        // repeatedly request more than available without waiting for refill
        for (let i=0;i<steps;i++){
          const req = max + tokens;
          const ok = await rl.consume(req);
          expect(ok).toBe(false);
          const count = rl.getTokenCount();
          expect(count).toBeGreaterThanOrEqual(0);
          expect(count).toBeLessThanOrEqual(max);
        }
      }
    ), { numRuns: 30 });
  });
});
