import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket tiny interval long waits (fast)', () => {
  it(formatGWT('tiny interval', 'waits of 2*interval only', 'tokens within [0,max] for 4 steps'), async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({ tokens: fc.integer({ min: 1, max: 4 }), interval: fc.integer({ min: 6, max: 18 }), max: fc.integer({ min: 5, max: 20 }) }),
        async ({ tokens, interval, max }) => {
          const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
          await rl.consume(Math.min(max, Math.ceil(max/2)));
          for (let i=0;i<4;i++) {
            await rl.consume(max + tokens).catch(()=>void 0);
            let c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);
            await new Promise(r=>setTimeout(r, Math.min(2*interval, interval + 25)));
            c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);
          }
        }
      ),
      { numRuns: 8 }
    );
  });
});

