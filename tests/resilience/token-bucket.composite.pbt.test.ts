import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket composite scenario (oversubscribe + varied waits)', () => {
  it('composite flow stays within [0,max] and respects capacity', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 10 }), interval: fc.integer({ min: 10, max: 80 }), max: fc.integer({ min: 5, max: 50 }), steps: fc.integer({ min: 2, max: 6 }) }),
      async ({ tokens, interval, max, steps }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        // Start partially drained
        await rl.consume(Math.min(max, Math.ceil(max/2)));
        for (let i=0;i<steps;i++){
          // Random-ish consume size around capacity boundaries
          const req = Math.max(1, Math.min(max + tokens, Math.ceil(max/2) + i));
          await rl.consume(req); // may fail internally
          let c = rl.getTokenCount();
          expect(c).toBeGreaterThanOrEqual(0);
          expect(c).toBeLessThanOrEqual(max);
          // Wait 0..interval (skewed)
          const wait = (i % 2 === 0) ? Math.floor(interval/3) : interval + 5;
          await new Promise(r => setTimeout(r, wait));
          c = rl.getTokenCount();
          expect(c).toBeGreaterThanOrEqual(0);
          expect(c).toBeLessThanOrEqual(max);
        }
      }
    ), { numRuns: 20 });
  });
});

