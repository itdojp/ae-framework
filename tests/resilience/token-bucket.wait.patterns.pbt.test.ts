import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket varied wait patterns', () => {
  it('after varied waits, tokens remain within [0,max]', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 10 }), interval: fc.integer({ min: 10, max: 80 }), max: fc.integer({ min: 5, max: 50 }) }),
      async ({ tokens, interval, max }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        await rl.consume(Math.min(max, Math.ceil(max/2)));
        const waits = [Math.floor(interval/4), Math.floor(interval/2), interval+5, interval*2+5];
        for (const w of waits) {
          await new Promise(r => setTimeout(r, w));
          const c = rl.getTokenCount();
          expect(c).toBeGreaterThanOrEqual(0);
          expect(c).toBeLessThanOrEqual(max);
        }
      }
    ), { numRuns: 20 });
  });
});

