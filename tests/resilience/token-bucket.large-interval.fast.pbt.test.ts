import { describe, it, expect } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket large interval (fast)', () => {
  it(formatGWT('partial drain', 'steps with large waits', 'tokens within [0,max] over 4 steps'), async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({ tokens: fc.integer({ min: 1, max: 8 }), interval: fc.integer({ min: 80, max: 200 }), max: fc.integer({ min: 6, max: 60 }) }),
        async ({ tokens, interval, max }) => {
          const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
          await rl.consume(Math.min(max, Math.ceil(max/2)));
          for (let i=0;i<4;i++){
            await rl.consume(max + tokens).catch(()=>void 0);
            let c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);
            await new Promise(r=>setTimeout(r, Math.floor(interval/2)));
            c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);
          }
        }
      ),
      { numRuns: 10 }
    );
  });
});
