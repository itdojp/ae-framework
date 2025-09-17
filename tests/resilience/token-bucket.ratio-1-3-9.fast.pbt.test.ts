import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket ratio 1:3:9 sequence (fast)', () => {
  it(
    formatGWT('tiny interval', 'apply waits [1, i*3, i*9]', 'tokens within [0..max]'),
    async () => {
      const i = 7;
      const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval: i, maxTokens: 4 });
      // Drain
      for (let k = 0; k < 4; k++) await rl.consume(1).catch(() => void 0);
      const waits = [1, i * 3, i * 9];
      for (const w of waits) {
        await new Promise(r => setTimeout(r, w));
        await rl.consume(1).catch(() => void 0);
        const t = rl.getTokenCount();
        expect(t).toBeGreaterThanOrEqual(0);
        expect(t).toBeLessThanOrEqual(4);
      }
    }
  );
});

