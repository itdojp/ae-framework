import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket composite mixed pattern (fast)', () => {
  it(
    formatGWT('tiny interval', 'use waits [1, i/2, i*3, 1, i*2]', 'tokens stay within [0..max]'),
    async () => {
      const i = 12;
      const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval: i, maxTokens: 4 });
      // Drain initial tokens
      for (let k = 0; k < 4; k++) await rl.consume(1).catch(() => void 0);
      const waits = [1, Math.floor(i / 2), i * 3, 1, i * 2];
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

