import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket ratio 1:5:10:20 (fast)', () => {
  it(
    formatGWT('tiny interval', 'apply waits [1, i*5, i*10, i*20]', 'tokens remain within [0..max]'),
    async () => {
      const i = 5;
      const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval: i, maxTokens: 4 });
      for (let k = 0; k < 4; k++) await rl.consume(1).catch(() => void 0);
      const waits = [1, i*5, i*10, i*20];
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

