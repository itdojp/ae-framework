import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket oversubscribe alternating with waits', () => {
  it('tokens remain within [0,max] under alternating consume/wait cycles', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 10 }), interval: fc.integer({ min: 10, max: 40 }), max: fc.integer({ min: 5, max: 50 }) }),
      async ({ tokens, interval, max }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        for (let i=0;i<5;i++){
          try { await rl.consume(max + 1); } catch {}
          await new Promise(r => setTimeout(r, Math.floor(interval * (0.5 + (i%2?1:0)))));
          const c = rl.getTokenCount();
          expect(c).toBeGreaterThanOrEqual(0);
          expect(c).toBeLessThanOrEqual(max);
        }
      }
    ), { numRuns: 10 });
  });
});

