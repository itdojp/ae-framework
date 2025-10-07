import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('TokenBucket burst then refill capacity cap (fast)', () => {
  it('rejects over-capacity bursts and allows exact after refills', async () => {
    const max = 6;
    const rl = new TokenBucketRateLimiter({ tokensPerInterval: 2, interval: 5, maxTokens: max });
    // initial burst over capacity should fail
    const over = await rl.consume(max + 2);
    expect(over).toBe(false);
    // wait multiple intervals to refill
    for (let i = 0; i < 3; i++) await new Promise(r => setTimeout(r, 6));
    // exact capacity should be allowed
    const exact = await rl.consume(max);
    expect(exact).toBe(true);
  });
});

