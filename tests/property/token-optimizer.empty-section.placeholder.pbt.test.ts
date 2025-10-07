import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

const SECTIONS = ['product', 'design', 'architecture', 'standards'] as const;

const whitespaceArb = fc.constantFrom('', ' ', '\n', '\t', '  ', '\r\n');

const emptySectionDocs = fc.subarray(SECTIONS, { minLength: 1, maxLength: SECTIONS.length }).chain((keys) =>
  fc.array(whitespaceArb, { minLength: keys.length, maxLength: keys.length }).map((values) => {
    const docs: Record<string, string> = {};
    keys.forEach((key, index) => {
      docs[key] = values[index];
    });
    return docs;
  })
);

describe('PBT: TokenOptimizer empty sections placeholder', () => {
  it('inserts [EMPTY] placeholder when section content is blank or whitespace', async () => {
    await fc.assert(
      fc.asyncProperty(emptySectionDocs, async (docs) => {
        const optimizer = new TokenOptimizer();
        const { compressed } = await optimizer.compressSteeringDocuments(docs, {
          enableCaching: false,
          preservePriority: SECTIONS as unknown as string[],
        });

        expect(compressed).toContain('[EMPTY]');
      }),
      { numRuns: 25 }
    );
  });
});
