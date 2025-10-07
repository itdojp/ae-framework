import { describe, it, expect } from 'vitest';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

// Fast, deterministic boundary check (+1 beyond caps)
describe('TokenBucket boundary +1 (fast)', () => {
  it('never exceeds maxTokens and guards +1 edge', async () => {
    const maxTokens = 3;
    const rl = new TokenBucketRateLimiter({ tokensPerInterval: 2, interval: 5, maxTokens });
    // Immediately attempt more than capacity
    const allowed1 = await rl.consume(maxTokens + 1);
    expect(allowed1).toBe(false);
    // Consume exactly capacity
    const allowed2 = await rl.consume(maxTokens);
    expect(allowed2).toBe(true);
    // Wait a short interval to refill (best-effort)
    await new Promise((r) => setTimeout(r, 6));
    // After refill, still must not allow beyond max
    const allowed3 = await rl.consume(maxTokens + 1);
    expect(allowed3).toBe(false);
  });
});

