import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('TokenBucket capacity cap after many intervals (fast)', () => {
  it('never exceeds maxTokens even after many refills', async () => {
    const maxTokens = 5;
    const rl = new TokenBucketRateLimiter({ tokensPerInterval: 3, interval: 5, maxTokens });
    // drain
    await rl.consume(maxTokens);
    // wait multiple intervals
    for (let i = 0; i < 4; i++) await new Promise(r => setTimeout(r, 6));
    // now attempt to remove more than capacity
    const allowed = await rl.consume(maxTokens + 1);
    expect(allowed).toBe(false);
    // exactly capacity should be allowed
    const allowedExact = await rl.consume(maxTokens);
    expect(allowedExact).toBe(true);
  });
});

