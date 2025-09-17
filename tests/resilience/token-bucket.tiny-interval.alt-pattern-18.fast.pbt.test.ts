import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import fc from 'fast-check';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket tiny-interval alt pattern 18 (fast)', () => {
  it(
    formatGWT('tiny interval', 'apply waits [i, i/2, 1, i/3]', 'tokens within [0..max]'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.integer({ min: 2, max: 5 }),
          fc.integer({ min: 1, max: 3 }),
          async (maxTokens, per) => {
            const i = 6;
            const rl = new TokenBucketRateLimiter({ tokensPerInterval: per, interval: i, maxTokens });
            // drain
            for (let k = 0; k < maxTokens; k++) await rl.consume(1).catch(() => void 0);
            const waits = [i, Math.max(1, Math.floor(i/2)), 1, Math.max(1, Math.floor(i/3))];
            for (const w of waits) {
              await new Promise((r) => setTimeout(r, w));
              await rl.consume(1).catch(() => void 0);
              const t = rl.getTokenCount();
              expect(t).toBeGreaterThanOrEqual(0);
              expect(t).toBeLessThanOrEqual(maxTokens);
            }
          }
        ),
        { numRuns: 8 }
      );
    }
  );
});

