import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket alternating oversubscribe with waits', () => {
  it('alternating oversubscribe/await patterns never go negative or exceed max', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          tokens: fc.integer({ min: 1, max: 10 }),
          interval: fc.integer({ min: 10, max: 80 }),
          max: fc.integer({ min: 5, max: 60 }),
          steps: fc.integer({ min: 3, max: 10 }),
        }),
        async ({ tokens, interval, max, steps }) => {
          const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
          // Begin with a partial drain to avoid trivial full bucket behavior
          await rl.consume(Math.min(max, Math.ceil(max / 2)));
          let last = rl.getTokenCount();
          expect(last).toBeGreaterThanOrEqual(0);
          expect(last).toBeLessThanOrEqual(max);

          for (let i = 0; i < steps; i++) {
            // Oversubscribe request alternates around capacity boundaries
            const req = i % 2 === 0 ? max + tokens : Math.max(1, Math.ceil(max / 3));
            await rl.consume(req).catch(() => void 0); // may fail internally; invariants still must hold
            let c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);

            // Alternate waits: short vs ~interval with slight slack
            const wait = i % 2 === 0 ? Math.floor(interval / 2) : interval + 7;
            await new Promise((r) => setTimeout(r, wait));
            c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);
            // Monotonicity not guaranteed, but ensure no wild swings beyond bounds
            last = c;
          }
        }
      ),
      { numRuns: 10 }
    );
  });
});
