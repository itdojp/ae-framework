import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenBucket tiny interval mixed very short waits (fast)', () => {
  it(
    formatGWT('tiny interval ~10–16ms', 'alternate waits 1ms/interval/2/interval', 'token count remains within [0..max]'),
    async () => {
      const interval = 12; // tiny interval in ms
      const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval, maxTokens: 4 });

      // Drain initial tokens
      for (let i = 0; i < 4; i++) {
        await rl.consume(1);
      }

      const waits = [1, Math.floor(interval / 2), interval, 1, interval * 2, Math.max(1, interval - 1)];
      for (const w of waits) {
        await new Promise((r) => setTimeout(r, w));
        // Observe and optionally consume; only invariants matter
        const _ok = await rl.consume(1);
        const t = rl.getTokenCount();
        expect(t).toBeGreaterThanOrEqual(0);
        expect(t).toBeLessThanOrEqual(4);
      }
    }
  );
});

