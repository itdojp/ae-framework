import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import fc from 'fast-check';

describe('PBT: TokenOptimizer present-only sections (large alt4)', () => {
  it('output includes only present sections and priority order preserved', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          product: fc.option(fc.string({ minLength: 50, maxLength: 300 }), { nil: undefined }),
          architecture: fc.option(fc.string({ minLength: 50, maxLength: 300 }), { nil: undefined }),
          standards: fc.option(fc.string({ minLength: 50, maxLength: 300 }), { nil: undefined }),
          misc: fc.option(fc.string({ minLength: 50, maxLength: 300 }), { nil: undefined })
        }),
        async (docs) => {
          const opt = new TokenOptimizer();
          const { compressed } = await opt.compressSteeringDocuments(docs as any, { maxTokens: 800, compressionLevel: 'medium' });
          const present = Object.entries(docs).filter(([_, v]) => typeof v === 'string');
          // ensure missing are not present
          for (const [name, v] of Object.entries(docs)) {
            if (!v) {
              expect(compressed).not.toMatch(new RegExp(`^## ${name.toUpperCase()}`, 'm'));
            }
          }
          // ensure priority order among present priority sections
          const order = ['PRODUCT', 'ARCHITECTURE', 'STANDARDS'];
          const presentPriority = order.filter(h => present.some(([n]) => n.toUpperCase() === h));
          const idx = presentPriority.map(h => compressed.indexOf(`\n## ${h}\n`)).filter(i => i >= 0);
          const sorted = [...idx].sort((a,b)=>a-b);
          expect(idx).toEqual(sorted);
        }
      ),
      { numRuns: 8 }
    );
  });
});

