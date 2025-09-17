import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import fc from 'fast-check';

describe('PBT: TokenOptimizer truncate boundary (large)', () => {
  it('compressed estimateTokens should be <= maxTokens when max is small', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          product: fc.string({ minLength: 200, maxLength: 1200 }),
          architecture: fc.string({ minLength: 200, maxLength: 1200 }),
          standards: fc.string({ minLength: 200, maxLength: 1200 })
        }),
        async (docs) => {
          const opt = new TokenOptimizer();
          const maxTokens = 150; // intentionally small to trigger truncation
          const { compressed } = await opt.compressSteeringDocuments(docs as any, { maxTokens, compressionLevel: 'medium' });
          const est = opt.estimateTokens(compressed);
          expect(est).toBeLessThanOrEqual(maxTokens);
        }
      ),
      { numRuns: 6 }
    );
  });
});

