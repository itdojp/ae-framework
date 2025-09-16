import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('PBT: TokenOptimizer.optimizeContext', () => {
  it('optimized length does not exceed original and stats are consistent', async () => {
    const opt = new TokenOptimizer();
    await fc.assert(fc.asyncProperty(
      fc.record({
        context: fc.string({ minLength: 0, maxLength: 500 }),
        maxTokens: fc.integer({ min: 50, max: 1000 }),
        keywords: fc.array(fc.string({ minLength: 1, maxLength: 6 }), { maxLength: 5 })
      }),
      async ({ context, maxTokens, keywords }) => {
        const { optimized, stats } = await opt.optimizeContext(context, maxTokens, keywords);
        expect(optimized.length).toBeLessThanOrEqual(context.length);
        expect(stats.original).toBeGreaterThanOrEqual(stats.compressed);
        expect(stats.reductionPercentage).toBeGreaterThanOrEqual(0);
        expect(stats.reductionPercentage).toBeLessThanOrEqual(100);
      }
    ), { numRuns: 30 });
  });
});

