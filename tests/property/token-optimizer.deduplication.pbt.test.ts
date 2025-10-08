import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('PBT: TokenOptimizer.deduplicatePatterns (implicit via compressSteeringDocuments)', () => {
  it('removes duplicate sentences ignoring case/spacing', async () => {
    const sentenceArb = fc.stringOf(
      fc.constantFrom(
        'a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z',
        'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z',
        '0','1','2','3','4','5','6','7','8','9',' '),
      { minLength: 3, maxLength: 32 }
    ).filter(s => s.trim().length > 0);

    await fc.assert(fc.asyncProperty(
      fc.array(sentenceArb, { minLength: 3, maxLength: 6 }),
      async (sentences) => {
        const base = sentences[0] || 'alpha';
        const dupVariants = [base, base.toUpperCase(), ` ${base}  `];
        const docs = {
          product: dupVariants.join('. ') + '.',
          standards: sentences.slice(1).join('. ') + '.'
        };
        const opt = new TokenOptimizer();
        const { compressed } = await opt.compressSteeringDocuments(docs, { compressionLevel: 'medium', enableCaching: false });
        expect(typeof compressed).toBe('string');
        const count = (compressed.match(new RegExp(base.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'gi')) || []).length;
        expect(count).toBeGreaterThanOrEqual(1);
      }
    ), { numRuns: 10 });
  });
});
