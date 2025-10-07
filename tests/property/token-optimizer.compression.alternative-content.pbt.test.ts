import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer compression on alternative content', () => {
  it(
    formatGWT('mixed headers/bullets/code', 'compressSteeringDocuments', 'dedup; headers first; tokens reduced or equal'),
    async () => {
      const uniqueKeysArb = fc
        .array(fc.constantFrom('product', 'design', 'architecture', 'standards'), { minLength: 2, maxLength: 4 })
        .map((a) => Array.from(new Set(a)));

      await fc.assert(
        fc.asyncProperty(uniqueKeysArb, async (keys) => {
          const docs: Record<string, string> = {};
          const fence = ['```', 'code fence', '```'].join('\n');
          for (const k of keys) {
            docs[k] = [
              `# ${k}`,
              '- bullet A',
              '- bullet A',
              fence,
              'paragraph paragraph paragraph',
              'paragraph paragraph paragraph',
            ].join('\n');
          }
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(docs, {
            preservePriority: ['product', 'design', 'architecture', 'standards'],
            maxTokens: 4000,
            enableCaching: false,
          });
          const body = res.compressed;
          const idx = ['PRODUCT', 'DESIGN', 'ARCHITECTURE', 'STANDARDS']
            .map((h) => body.indexOf('## ' + h))
            .filter((i) => i >= 0);
          for (let i = 1; i < idx.length; i++) expect(idx[i - 1]).toBeLessThan(idx[i]);
          const dedupedCount = (body.match(/- bullet A/g) || []).length;
          expect(dedupedCount).toBeLessThanOrEqual(keys.length * 2);
          expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
        }),
        { numRuns: 6 }
      );
    }
  );
});
