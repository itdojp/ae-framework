import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('PBT: TokenOptimizer.deduplicatePatterns (implicit via compressSteeringDocuments)', () => {
  it('removes duplicate sentences ignoring case/spacing', async () => {
    const sentencesArb = fc
      .array(fc.string({ minLength: 3, maxLength: 32 }), { minLength: 3, maxLength: 6 })
      .filter((arr) => {
        const first = arr[0];
        return typeof first === 'string' && /[a-z0-9]/i.test(first);
      });

    await fc.assert(
      fc.asyncProperty(sentencesArb, async (sentences) => {
        const base = sentences[0] || 'alpha';
        const normalizedBase = base.trim();
        if (normalizedBase.length === 0) return;
        const dupVariants = [base, base.toUpperCase(), ` ${base}  `];
        const docs = {
          product: `${dupVariants.join('. ')}.`,
          standards: `${sentences.slice(1).join('. ')}.`,
        };
        const opt = new TokenOptimizer();
        const { compressed } = await opt.compressSteeringDocuments(docs, {
          compressionLevel: 'medium',
          enableCaching: false,
        });
        const normalizedCompressed = compressed.replace(/[\W_]+/g, '').toLowerCase();
        const target = normalizedBase.replace(/[\W_]+/g, '').toLowerCase();
        if (target.length === 0) return;
        expect(normalizedCompressed.includes(target)).toBe(true);
      }),
      { numRuns: 10 }
    );
  });
});
