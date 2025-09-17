import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket tiny-interval alt-pattern-15 (fast)', () => {
  it(
    formatGWT('tiny interval with varied short waits', 'acquire', '[0..max] invariant across alternating waits'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.integer({ min: 2, max: 5 }), // maxTokens
          fc.integer({ min: 1, max: 3 }), // tokensPerInterval
          async (maxTokens, per) => {
            const interval = 5; // tiny interval (ms)
            const rl = new TokenBucketRateLimiter({ maxTokens, tokensPerInterval: per, interval });
            // Drain available tokens
            for (let i = 0; i < maxTokens; i++) await rl.consume(1).catch(() => void 0);
            // alt-pattern-15: 1 → interval/2 → interval → 2*interval → 1
            const waits = [1, Math.max(1, Math.floor(interval / 2)), interval, 2 * interval, 1];
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
