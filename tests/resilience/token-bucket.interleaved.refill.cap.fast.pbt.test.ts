import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('TokenBucket interleaved refill respects maxTokens (fast)', () => {
  it('never exceeds capacity with interleaved remove/wait cycles', async () => {
    const maxTokens = 4;
    const rl = new TokenBucketRateLimiter({ tokensPerInterval: 2, interval: 5, maxTokens });
    // remove 3 tokens if possible
    rl.tryRemoveTokens(3);
    // wait one interval
    await new Promise(r => setTimeout(r, 6));
    // attempt to remove > capacity
    const over = rl.tryRemoveTokens(maxTokens + 1);
    expect(over).toBe(false);
    // exactly capacity should eventually work after refills
    await new Promise(r => setTimeout(r, 6));
    const ok = rl.tryRemoveTokens(maxTokens);
    expect(ok).toBe(true);
  });
});

