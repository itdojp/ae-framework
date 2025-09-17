import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import fc from 'fast-check';

describe('PBT: TokenOptimizer compress maxTokens monotonicity', () => {
  it('compressed tokens should not decrease when maxTokens increases', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          product: fc.string({ minLength: 300, maxLength: 1200 }),
          architecture: fc.string({ minLength: 300, maxLength: 1200 }),
          standards: fc.string({ minLength: 300, maxLength: 1200 })
        }),
        async (docs) => {
          const opt = new TokenOptimizer();
          const small = await opt.compressSteeringDocuments(docs as any, { maxTokens: 500, compressionLevel: 'medium' });
          const large = await opt.compressSteeringDocuments(docs as any, { maxTokens: 1000, compressionLevel: 'medium' });
          expect(large.stats.compressed).toBeGreaterThanOrEqual(small.stats.compressed);
        }
      ),
      { numRuns: 6 }
    );
  });
});

