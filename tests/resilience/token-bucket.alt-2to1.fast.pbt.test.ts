import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket alternation ratio 2:1 (fast)', () => {
  it(
    formatGWT('tiny interval', 'alternate waits interval*2 / interval', 'tokens remain within [0..max]'),
    async () => {
      const interval = 12;
      const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval, maxTokens: 4 });
      await rl.consume(4).catch(() => void 0);
      const waits = [interval * 2, interval, interval * 2, interval, interval * 2];
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

