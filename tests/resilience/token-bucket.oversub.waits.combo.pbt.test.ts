import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket oversubscribe with varied waits', () => {
  it('tokens remain within [0,max] across oversubscribe and waits', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 10 }), interval: fc.integer({ min: 10, max: 40 }), max: fc.integer({ min: 5, max: 50 }) }),
      async ({ tokens, interval, max }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        // Oversubscribe sequence
        const ask = Math.min(max + 2, max * 2);
        try { await rl.consume(ask); } catch {}
        // Wait patterns: /3, /2, 1×, 2×, 3×
        const waits = [Math.floor(interval/3), Math.floor(interval/2), interval, interval*2];
        for (const w of waits) {
          await new Promise(r => setTimeout(r, w));
          const c = rl.getTokenCount();
          expect(c).toBeGreaterThanOrEqual(0);
          expect(c).toBeLessThanOrEqual(max);
        }
      }
    ), { numRuns: 10 });
  });
});
