import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket tiny-interval alt-pattern-18 (fast)', () => {
  it(
    formatGWT('tiny interval varied waits', 'apply waits [1, i, i/3, 2i]', 'tokens within [0,max]'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.integer({ min: 2, max: 6 }),
          fc.integer({ min: 1, max: 3 }),
          async (maxTokens, per) => {
            const interval = 9;
            const rl = new TokenBucketRateLimiter({ maxTokens, tokensPerInterval: per, interval });
            for (let i = 0; i < maxTokens; i++) await rl.consume(1).catch(() => void 0);
            const waits = [1, interval, Math.max(1, Math.floor(interval/3)), 2*interval];
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

