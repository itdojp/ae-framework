import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('PBT: TokenOptimizer optimizeContext respects maxTokens', () => {
  const lorem = 'Lorem ipsum dolor sit amet, consectetur adipiscing elit. ';
  it('optimizeContext never exceeds maxTokens (estimation)', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          repeats: fc.integer({ min: 1, max: 40 }),
          maxTokens: fc.integer({ min: 50, max: 500 }),
          kws: fc.array(fc.string({ minLength: 1, maxLength: 6 }), { minLength: 0, maxLength: 4 })
        }),
        async ({ repeats, maxTokens, kws }) => {
          const opt = new TokenOptimizer();
          const ctx = lorem.repeat(repeats);
          const { optimized, stats } = await opt.optimizeContext(ctx, maxTokens, kws);
          // estimation invariant: optimized tokens <= maxTokens
          expect(stats.compressed).toBeLessThanOrEqual(maxTokens);
          // sanity: output is string
          expect(typeof optimized).toBe('string');
        }
      ),
      { numRuns: 30 }
    );
  });
});

