import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import fc from 'fast-check';

describe('PBT: TokenOptimizer optimizeContext monotonicity (tokens)', () => {
  it('optimized tokens should not decrease when maxTokens increases', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.string({ minLength: 200, maxLength: 1200 }),
        fc.array(fc.string({ minLength: 3, maxLength: 10 }), { minLength: 0, maxLength: 5 }),
        async (text, keywords) => {
          const opt = new TokenOptimizer();
          const small = await opt.optimizeContext(text, 200, keywords);
          const large = await opt.optimizeContext(text, 400, keywords);
          expect(large.stats.compressed).toBeGreaterThanOrEqual(small.stats.compressed);
        }
      ),
      { numRuns: 10 }
    );
  });
});

