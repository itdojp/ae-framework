import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('Resilience: TokenBucket tiny-interval alternate short waits (fast)', () => {
  it('tokens remain within [0..max] under alternating short waits', async () => {
    const interval = 12; // tiny interval (ms)
    const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval, maxTokens: 3 });

    // Start by draining tokens quickly
    for (let i = 0; i < 3; i++) {
      await rl.consume(1);
    }

    const waits = [1, Math.floor(interval / 6), Math.floor(interval / 3), 1, Math.floor(interval / 2), interval, 1];
    for (const w of waits) {
      // alternate consume/wait/consume ensuring bounds stay valid
      await new Promise((r) => setTimeout(r, Math.max(0, w)));
      const ok = await rl.consume(1);
      const t = rl.getTokenCount();
      expect(t).toBeGreaterThanOrEqual(0);
      expect(t).toBeLessThanOrEqual(3);
      // When consume failed (no token yet), wait a bit more to avoid flakiness and try again
      if (!ok) {
        await new Promise((r) => setTimeout(r, Math.max(1, interval - w)));
        const ok2 = await rl.consume(1);
        const t2 = rl.getTokenCount();
        expect(t2).toBeGreaterThanOrEqual(0);
        expect(t2).toBeLessThanOrEqual(3);
        // No strict success requirement here; only invariants on token bounds
      }
    }
  });
});
