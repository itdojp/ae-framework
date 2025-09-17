import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

// Fast PBT-ish check with fixed pattern to keep CI stable
describe('PBT: TokenBucket ratio 1:3:9:18 (reorder, fast)', () => {
  it(
    formatGWT('tiny interval', 'apply waits [i*9, 1, i*3, i*18] (reordered)', 'tokens within [0..max]'),
    async () => {
      const i = 4; // tiny interval
      const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval: i, maxTokens: 4 });
      // drain to 0 (ignore initial rejects)
      for (let k = 0; k < 4; k++) await rl.consume(1).catch(() => void 0);
      const waits = [i * 9, 1, i * 3, i * 18];
      for (const w of waits) {
        await new Promise((r) => setTimeout(r, w));
        await rl.consume(1).catch(() => void 0);
        const t = rl.getTokenCount();
        expect(t).toBeGreaterThanOrEqual(0);
        expect(t).toBeLessThanOrEqual(4);
      }
    }
  );
});

