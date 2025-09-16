import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket oversubscribe alternating with partial replenish', () => {
  it('alternating consume/wait keeps tokens within [0,max] and respects limits', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 10 }), interval: fc.integer({ min: 10, max: 60 }), max: fc.integer({ min: 5, max: 50 }), steps: fc.integer({ min: 2, max: 5 }) }),
      async ({ tokens, interval, max, steps }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        // drain fully first
        await rl.consume(max);
        for (let i=0;i<steps;i++){
          // request may exceed available
          const req = Math.min(max + tokens, Math.max(1, Math.floor(max/2))) + i; // vary a little
          const ok = await rl.consume(req);
          // if ok, we consumed within bounds; if not ok, bucket should stay >=0
          const countAfterConsume = rl.getTokenCount();
          expect(countAfterConsume).toBeGreaterThanOrEqual(0);
          expect(countAfterConsume).toBeLessThanOrEqual(max);
          // wait for partial replenish (~ half interval)
          await new Promise(r => setTimeout(r, Math.floor(interval/2) + 5));
          const countAfterWait = rl.getTokenCount();
          expect(countAfterWait).toBeGreaterThanOrEqual(0);
          expect(countAfterWait).toBeLessThanOrEqual(max);
        }
      }
    ), { numRuns: 20 });
  });
});

