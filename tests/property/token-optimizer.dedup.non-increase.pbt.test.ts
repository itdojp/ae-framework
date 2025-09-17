import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import fc from 'fast-check';

describe('PBT: TokenOptimizer deduplication does not increase tokens', () => {
  it('after compression (medium), tokens <= original estimate', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.array(fc.string({ minLength: 10, maxLength: 50 }), { minLength: 10, maxLength: 50 }),
        async (arr) => {
          const repeated = arr.concat(arr).join('. ') + '.';
          const docs = { product: repeated, architecture: repeated, standards: repeated } as any;
          const opt = new TokenOptimizer();
          const originalEst = opt.estimateTokens(JSON.stringify(docs));
          const { stats } = await opt.compressSteeringDocuments(docs, { maxTokens: 2000, compressionLevel: 'medium' });
          expect(stats.compressed).toBeLessThanOrEqual(originalEst);
        }
      ),
      { numRuns: 6 }
    );
  });
});

