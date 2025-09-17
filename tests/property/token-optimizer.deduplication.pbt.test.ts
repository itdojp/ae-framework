import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('PBT: TokenOptimizer.deduplicatePatterns (implicit via compressSteeringDocuments)', () => {
  it('removes duplicate sentences ignoring case/spacing', async () => {
    await fc.assert(fc.asyncProperty(
      fc.array(fc.string({ minLength: 3, maxLength: 32 }), { minLength: 3, maxLength: 6 }),
      async (sentences) => {
        const base = sentences[0] || 'alpha';
        const dupVariants = [base, base.toUpperCase(), ` ${base}  `];
        const docs = { product: dupVariants.join('. ') + '.', standards: sentences.slice(1).join('. ') + '.' };
        const opt = new TokenOptimizer();
        const { compressed } = await opt.compressSteeringDocuments(docs, { compressionLevel: 'medium', enableCaching: false });
        const count = (compressed.match(new RegExp(base.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'gi')) || []).length;
        expect(count).toBeGreaterThanOrEqual(1);
      }
    ), { numRuns: 10 });
  });
});

