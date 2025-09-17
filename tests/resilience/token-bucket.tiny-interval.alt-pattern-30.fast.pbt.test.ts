import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

// Tiny-interval alternate pattern (fast, numRuns控えめ)
describe('TokenBucket tiny-interval alt-pattern-30 (fast)', () => {
  it('tokens remain within [0..max] under mixed waits', async () => {
    const maxTokens = 5;
    const rl = new TokenBucketRateLimiter({ tokensPerInterval: 2, interval: 5, maxTokens });
    // consume some
    await rl.consume(3);
    // short wait
    await new Promise(r => setTimeout(r, 3));
    // attempt over max (should fail)
    const over = await rl.consume(maxTokens + 1);
    expect(over).toBe(false);
    // wait full interval to refill
    await new Promise(r => setTimeout(r, 6));
    // consume exactly capacity (should succeed)
    const ok = await rl.consume(maxTokens);
    expect(ok).toBe(true);
    // final check
    const count = rl.getTokenCount();
    expect(count).toBeGreaterThanOrEqual(0);
    expect(count).toBeLessThanOrEqual(maxTokens);
  });
});

