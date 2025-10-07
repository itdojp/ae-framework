import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('TokenBucket interleaved refill respects maxTokens (fast)', () => {
  it('never exceeds capacity with interleaved remove/wait cycles', async () => {
    const maxTokens = 4;
    const rl = new TokenBucketRateLimiter({ tokensPerInterval: 2, interval: 5, maxTokens });
    // remove 3 tokens if possible
    await rl.consume(3);
    // wait one interval
    await new Promise(r => setTimeout(r, 6));
    // attempt to remove > capacity
    const over = await rl.consume(maxTokens + 1);
    expect(over).toBe(false);
    // exactly capacity should eventually work after refills
    await new Promise(r => setTimeout(r, 6));
    const ok = await rl.consume(maxTokens);
    expect(ok).toBe(true);
  });
});

