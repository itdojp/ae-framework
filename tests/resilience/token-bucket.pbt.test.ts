import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenBucketRateLimiter } from '../../src/resilience/backoff-strategies';

describe('PBT: TokenBucketRateLimiter', () => {
  it('never returns negative tokens and does not exceed maxTokens', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 50 }), interval: fc.integer({ min: 1, max: 50 }), max: fc.integer({ min: 1, max: 100 }) }),
      async ({ tokens, interval, max }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        // consume more than max to force floor at 0
        const ok = await rl.consume(max + tokens);
        expect(typeof ok).toBe('boolean');
        const count = rl.getTokenCount();
        expect(count).toBeGreaterThanOrEqual(0);
        expect(count).toBeLessThanOrEqual(max);
      }
    ), { numRuns: 50 });
  });
  it('waitForTokens eventually completes without violating bounds', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({ tokens: fc.integer({ min: 1, max: 20 }), interval: fc.integer({ min: 5, max: 50 }), max: fc.integer({ min: 5, max: 50 }) }),
      async ({ tokens, interval, max }) => {
        const rl = new TokenBucketRateLimiter({ tokensPerInterval: tokens, interval, maxTokens: max });
        // drain
        await rl.consume(max);
        // request more than available
        const need = Math.min(tokens, max);
        const p = rl.waitForTokens(need);
        // Allow more than a single interval to avoid flakes on CI clocks
        await Promise.race([p, new Promise((_,rej)=>setTimeout(()=>rej(new Error('timeout')), interval*10))]);
        // waitForTokens internally consumes; just validate bounds
        const count = rl.getTokenCount();
        expect(count).toBeGreaterThanOrEqual(0);
        expect(count).toBeLessThanOrEqual(max);
      }
    ), { numRuns: 20 });
  });
});
