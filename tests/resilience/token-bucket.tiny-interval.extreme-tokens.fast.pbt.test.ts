import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket tiny interval with relatively large tokens (fast)', () => {
  it(formatGWT('tiny interval & larger tokens', '5 steps oversubscribe+wait', 'tokens within [0,max]'), async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({ tokens: fc.integer({ min: 2, max: 6 }), interval: fc.integer({ min: 6, max: 15 }), max: fc.integer({ min: 6, max: 18 }) }),
        async ({ tokens, interval, max }) => {
          const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
          await rl.consume(Math.min(max, Math.ceil(max/2)));
          for (let i=0;i<5;i++) {
            await rl.consume(max + tokens).catch(()=>void 0);
            let c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);
            await new Promise(r=>setTimeout(r, Math.floor(interval/3)));
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

