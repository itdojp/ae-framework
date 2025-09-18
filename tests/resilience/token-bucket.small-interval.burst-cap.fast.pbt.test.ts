import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('TokenBucket small-interval burst respects cap (fast)', () => {
  it('does not allow over-capacity removal after quick refills', async () => {
    const max = 3;
    const rl = new TokenBucketRateLimiter({ tokensPerInterval: 1, interval: 5, maxTokens: max });
    // drain
    rl.tryRemoveTokens(max);
    // quick refills
    await new Promise(r => setTimeout(r, 6));
    await new Promise(r => setTimeout(r, 6));
    // attempt over capacity
    const over = rl.tryRemoveTokens(max + 1);
    expect(over).toBe(false);
    // exact capacity should work after another refill step
    await new Promise(r => setTimeout(r, 6));
    const exact = rl.tryRemoveTokens(max);
    expect(exact).toBe(true);
  });
});

