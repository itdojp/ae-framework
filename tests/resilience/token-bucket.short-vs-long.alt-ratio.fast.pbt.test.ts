import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket short-vs-long alternation (1:3 ratio, fast)', () => {
  it(
    formatGWT('tiny interval', 'alternate waits 1ms / (interval*3)', 'tokens remain within [0..max]'),
    async () => {
      const interval = 10;
      const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval, maxTokens: 5 });
      // Drain initial tokens
      for (let i = 0; i < 5; i++) { await rl.consume(1); }
      const waits = [1, interval * 3, 1, interval * 3, 1, interval * 3];
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

