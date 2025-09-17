import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket alternating 5..8 steps (fast)', () => {
  it('tokens remain within [0,max] across 5..8 steps with varied waits', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          tokens: fc.integer({ min: 1, max: 8 }),
          interval: fc.integer({ min: 10, max: 60 }),
          max: fc.integer({ min: 6, max: 50 }),
          steps: fc.integer({ min: 5, max: 8 }),
        }),
        async ({ tokens, interval, max, steps }) => {
          const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
          // partial drain
          await rl.consume(Math.min(max, Math.ceil(max * 0.5)));
          for (let i=0;i<steps;i++){
            const req = (i % 2 === 0) ? max + tokens : Math.max(1, Math.ceil(max/3));
            await rl.consume(req).catch(() => void 0);
            let c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);
            const wait = (i % 2 === 0) ? Math.floor(interval/2) : interval;
            await new Promise(r => setTimeout(r, wait));
            c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);
          }
        }
      ),
      { numRuns: 12 }
    );
  });
});

