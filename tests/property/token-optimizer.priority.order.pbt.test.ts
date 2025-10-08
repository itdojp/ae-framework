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
        const sections = [
          { key: 'product', heading: '## PRODUCT', index: compressed.indexOf('## PRODUCT'), source: product },
          { key: 'architecture', heading: '## ARCHITECTURE', index: compressed.indexOf('## ARCHITECTURE'), source: architecture },
          { key: 'standards', heading: '## STANDARDS', index: compressed.indexOf('## STANDARDS'), source: standards }
        ];

        const present = sections.filter(section => section.index >= 0);
        // 少なくとも 1 セクションは出力される想定（空入力時は placeholder が挿入される）
        expect(present.length).toBeGreaterThan(0);
        for (let i = 1; i < present.length; i += 1) {
          expect(present[i].index).toBeGreaterThan(present[i - 1].index);
        }

        for (const missing of sections.filter(section => section.index < 0)) {
          expect((missing.source ?? '').trim().length).toBe(0);
        }
      }
    ), { numRuns: 10 });
  });
});

