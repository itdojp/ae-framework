import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket multi-ratio sequence (fast)', () => {
  it(
    formatGWT('tiny interval', 'apply waits [i, 2i, 4i, 1ms, i/2]', 'tokens remain within [0..max]'),
    async () => {
      const i = 10;
      const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval: i, maxTokens: 5 });
      // Drain initial tokens
      for (let k = 0; k < 5; k++) await rl.consume(1).catch(() => void 0);
      const waits = [i, i * 2, i * 4, 1, Math.max(1, Math.floor(i / 2))];
      for (const w of waits) {
        await new Promise((r) => setTimeout(r, w));
        await rl.consume(1).catch(() => void 0);
        const t = rl.getTokenCount();
        expect(t).toBeGreaterThanOrEqual(0);
        expect(t).toBeLessThanOrEqual(5);
      }
    }
  );
});

