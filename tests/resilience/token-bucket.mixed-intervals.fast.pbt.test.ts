import { describe, it, expect } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucket mixed intervals (fast)', () => {
  it(formatGWT('partial drain', 'alternate small/large waits', 'tokens within [0,max] for 5..7 steps'), async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({ tokens: fc.integer({ min: 1, max: 8 }), interval: fc.integer({ min: 12, max: 80 }), max: fc.integer({ min: 6, max: 50 }), steps: fc.integer({ min: 5, max: 7 }) }),
        async ({ tokens, interval, max, steps }) => {
          const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
          await rl.consume(Math.min(max, Math.ceil(max/2)));
          for (let i=0;i<steps;i++){
            const req = (i % 2 === 0) ? max + tokens : Math.max(1, Math.ceil(max/4));
            await rl.consume(req).catch(()=>void 0);
            let c = rl.getTokenCount();
            expect(c).toBeGreaterThanOrEqual(0);
            expect(c).toBeLessThanOrEqual(max);
            const wait = (i % 3 === 0) ? Math.floor(interval/3) : (i % 3 === 1) ? (2*interval) : interval;
            await new Promise(r=>setTimeout(r, wait));
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
