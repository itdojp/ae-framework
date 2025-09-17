import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket varied multi-cycle (fast)', () => {
  it(
    formatGWT('tiny interval', 'run 2 cycles of [i/4, i, 2i, 1ms]', 'tokens stay within [0..max]'),
    async () => {
      const interval = 12;
      const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval, maxTokens: 4 });
      await rl.consume(4).catch(() => void 0);
      const pattern = [Math.floor(interval / 4), interval, interval * 2, 1];
      for (let cycle = 0; cycle < 2; cycle++) {
        for (const w of pattern) {
          await new Promise((r) => setTimeout(r, w));
          await rl.consume(1).catch(() => void 0);
          const t = rl.getTokenCount();
          expect(t).toBeGreaterThanOrEqual(0);
          expect(t).toBeLessThanOrEqual(4);
        }
      }
    }
  );
});

