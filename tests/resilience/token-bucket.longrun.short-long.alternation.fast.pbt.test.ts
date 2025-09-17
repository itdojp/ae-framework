import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket long-run alternation (short/long waits, fast)', () => {
  it(
    formatGWT('tiny interval', 'alternate 1ms vs interval*2 for a few cycles', 'tokens remain within [0..max]'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.record({
            tokens: fc.integer({ min: 1, max: 3 }),
            interval: fc.integer({ min: 8, max: 16 }),
            max: fc.integer({ min: 3, max: 6 })
          }),
          async ({ tokens, interval, max }) => {
            const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
            // Drain initially
            await rl.consume(Math.min(max, tokens + 1));
            const waits = [1, interval * 2, 1, interval * 2, 1, interval * 2];
            for (const w of waits) {
              await new Promise(r => setTimeout(r, w));
              await rl.consume(1).catch(() => void 0);
              const t = rl.getTokenCount();
              expect(t).toBeGreaterThanOrEqual(0);
              expect(t).toBeLessThanOrEqual(max);
            }
          }
        ),
        { numRuns: 10 }
      );
    }
  );
});

