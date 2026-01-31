import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer mixed boundaries (large)', () => {
  const segmentArb = fc.oneof(
    fc.constantFrom(
      '# Header\n' + 'Text '.repeat(40),
      '- item a\n- item b\n- item c\n' + 'Note '.repeat(30),
      '```ts\n' + 'const x = 1;\n'.repeat(10) + '```\n',
      'Important: keep key points. '.repeat(35)
    ),
    fc.stringOf(fc.constantFrom('A', 'B', 'C', ' ', '\n', '-', '#', '*'), { minLength: 120, maxLength: 260 })
  );

  const sectionArb = fc.array(segmentArb, { minLength: 6, maxLength: 12 }).map((segments) =>
    segments.join('\n')
  );

  it(
    formatGWT(
      'mixed boundary inputs (headers/bullets/fences/text)',
      'compressSteeringDocuments with preservePriority',
      'all sections remain ordered and present'
    ),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.record({
            product: sectionArb,
            design: sectionArb,
            architecture: sectionArb,
            standards: sectionArb
          }),
          async (docs) => {
            const opt = new TokenOptimizer();
            const preservePriority = ['product', 'design', 'architecture', 'standards'];
            const res = await opt.compressSteeringDocuments(docs as Record<string, string>, {
              preservePriority,
              maxTokens: 6000,
              compressionLevel: 'medium',
              enableCaching: false
            });
            const body = res.compressed;
            const headers = preservePriority.map((k) => `## ${k.toUpperCase()}`);
            const indices = headers.map((h) => body.indexOf(h));
            for (const idx of indices) expect(idx).toBeGreaterThanOrEqual(0);
            for (let i = 1; i < indices.length; i++) expect(indices[i - 1]).toBeLessThan(indices[i]);
            for (const header of headers) {
              expect(body.split(header).length - 1).toBe(1);
            }
          }
        ),
        { numRuns: 6 }
      );
    }
  );
});
