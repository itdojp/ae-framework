import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('PBT: TokenOptimizer preservePriority ordering', () => {
  it('sections appear in preservePriority order when present', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({
        product: fc.string({ minLength: 1, maxLength: 64 }),
        design: fc.string({ minLength: 1, maxLength: 64 }),
        architecture: fc.string({ minLength: 1, maxLength: 64 }),
        standards: fc.string({ minLength: 1, maxLength: 64 }),
      }),
      async ({ product, design, architecture, standards }) => {
        const opt = new TokenOptimizer();
        const { compressed } = await opt.compressSteeringDocuments(
          { product, design, standards, architecture },
          {
            compressionLevel: 'low',
            enableCaching: false,
            preservePriority: ['product', 'design', 'architecture', 'standards'],
          }
        );

        const ordered = [
          { header: '## PRODUCT', index: compressed.indexOf('## PRODUCT') },
          { header: '## DESIGN', index: compressed.indexOf('## DESIGN') },
          { header: '## ARCHITECTURE', index: compressed.indexOf('## ARCHITECTURE') },
          { header: '## STANDARDS', index: compressed.indexOf('## STANDARDS') },
        ].filter(section => section.index >= 0);

        expect(ordered.length).toBeGreaterThan(0);
        for (let i = 1; i < ordered.length; i += 1) {
          expect(ordered[i].index).toBeGreaterThan(ordered[i - 1].index);
        }
      }
    ), { numRuns: 10 });
  });
});
