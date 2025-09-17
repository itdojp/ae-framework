import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket tiny-interval alt-pattern-16 (fast)', () => {
  it(
    formatGWT('tiny interval varied waits', 'acquire with interval/3→/6→1×→2×', 'tokens stay within [0,max]'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.integer({ min: 2, max: 5 }),
          fc.integer({ min: 1, max: 3 }),
          async (maxTokens, per) => {
            const interval = 6; // keep tiny and divisible by 3
            const rl = new TokenBucketRateLimiter({ maxTokens, tokensPerInterval: per, interval });
            // drain
            for (let i = 0; i < maxTokens; i++) await rl.consume(1).catch(() => void 0);
            const waits = [Math.max(1, Math.floor(interval/3)), Math.max(1, Math.floor(interval/6)), interval, 2*interval];
            for (const w of waits) {
              await new Promise((r) => setTimeout(r, w));
              await rl.consume(1).catch(() => void 0);
              const t = rl.getTokenCount();
              expect(t).toBeGreaterThanOrEqual(0);
              expect(t).toBeLessThanOrEqual(maxTokens);
            }
          }
        ),
        { numRuns: 10 }
      );
    }
  );
});

