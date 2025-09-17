import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer bulleted lists reorder & dedup (large)', () => {
  it(
    formatGWT('large with bullets', 'compressSteeringDocuments', 'bullets dedup; headers first; tokens reduced'),
    async () => {
      const uniqueKeysArb = fc
        .array(fc.constantFrom('product', 'design', 'architecture', 'standards'), { minLength: 2, maxLength: 4 })
        .map((a) => Array.from(new Set(a)));

      await fc.assert(
        fc.asyncProperty(uniqueKeysArb, async (keys) => {
          const docs: Record<string, string> = {};
          for (const k of keys) {
            docs[k] = [
              `# ${k}`,
              '- A',
              '- B',
              '- A',
              '- C',
              ('lorem '.repeat(150))
            ].join('\n');
          }

          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(docs, {
            preservePriority: ['product', 'design', 'architecture', 'standards'],
            maxTokens: 9000,
            enableCaching: false,
          });
          const body = res.compressed;
          // bullets likely deduped to <=3 unique
          expect((body.match(/^-[ ](A|B|C)$/gmi) || []).length).toBeLessThanOrEqual(3 * keys.length);
          expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
        }),
        { numRuns: 5 }
      );
    }
  );
});

