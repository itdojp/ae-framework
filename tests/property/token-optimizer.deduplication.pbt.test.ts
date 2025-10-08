import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('PBT: TokenOptimizer.deduplicatePatterns (implicit via compressSteeringDocuments)', () => {
  it('returns a string result for randomized steering documents', async () => {
    await fc.assert(fc.asyncProperty(
      fc.array(
        fc.string({ minLength: 3, maxLength: 32 }),
        { minLength: 2, maxLength: 6 }
      ),
      async (sentences) => {
        const dupVariants = sentences.slice(0, 2).map((s, index) => index === 0 ? s : ` ${s} `);
        const docs = {
          product: dupVariants.join('. ') + '.',
          standards: sentences.slice(1).join('. ') + '.'
        };
        const opt = new TokenOptimizer();
        const { compressed } = await opt.compressSteeringDocuments(docs, { compressionLevel: 'medium', enableCaching: false });
        expect(typeof compressed).toBe('string');
      }
    ), { numRuns: 10 });
  });
});
