import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket tiny-interval short variation 9 (fast)', () => {
  it(
    formatGWT('tiny interval', 'short waits [i/3, i/2, i, 3i]', 'tokens within [0..max]'),
    async () => {
      const i = 12;
      const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval: i, maxTokens: 3 });
      for (let k = 0; k < 3; k++) await rl.consume(1).catch(() => void 0);
      const waits = [Math.max(1, Math.floor(i/3)), Math.max(1, Math.floor(i/2)), i, 3*i];
      for (const w of waits) {
        await new Promise(r => setTimeout(r, w));
        await rl.consume(1).catch(() => void 0);
        const t = rl.getTokenCount();
        expect(t).toBeGreaterThanOrEqual(0);
        expect(t).toBeLessThanOrEqual(3);
      }
    }
  );
});
