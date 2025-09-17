import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket long-run alternating pattern', () => {
  it('sequence across 4..7 steps stays within [0,max] with varied waits (fast)', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          tokens: fc.integer({ min: 1, max: 10 }),
          interval: fc.integer({ min: 10, max: 50 }),
          max: fc.integer({ min: 6, max: 60 }),
          steps: fc.integer({ min: 4, max: 7 }),
        }),
        async ({ tokens, interval, max, steps }) => {
          const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
          // Start partially drained
          await rl.consume(Math.min(max, Math.ceil(max * 0.6)));
          for (let i = 0; i < steps; i++) {
            const req = (i % 3 === 0) ? max + tokens : (i % 3 === 1) ? Math.max(1, Math.ceil(max / 2)) : Math.max(1, Math.ceil(max / 4));
            await rl.consume(req).catch(() => void 0);
            let c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);
            const wait = (i % 3 === 0) ? Math.floor(interval / 3) : (i % 3 === 1) ? Math.floor((2 * interval) / 3) : interval;
            await new Promise((r) => setTimeout(r, wait));
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
