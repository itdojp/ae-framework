import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('PBT: TokenOptimizer preservePriority ordering', () => {
  it('sections appear in preservePriority order when present', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({
        product: fc.string({ minLength: 1, maxLength: 64 }),
        architecture: fc.string({ minLength: 1, maxLength: 64 }),
        standards: fc.string({ minLength: 1, maxLength: 64 }),
      }),
      async ({ product, architecture, standards }) => {
        const opt = new TokenOptimizer();
        const { compressed } = await opt.compressSteeringDocuments(
          { product, standards, architecture },
          { compressionLevel: 'low', enableCaching: false }
        );
        const idxProd = compressed.indexOf('## PRODUCT');
        const idxArch = compressed.indexOf('## ARCHITECTURE');
        const idxStd  = compressed.indexOf('## STANDARDS');
        expect(idxProd).toBeGreaterThanOrEqual(0);
        expect(idxArch).toBeGreaterThan(idxProd);
        expect(idxStd).toBeGreaterThan(idxArch);
      }
    ), { numRuns: 10 });
  });
});

