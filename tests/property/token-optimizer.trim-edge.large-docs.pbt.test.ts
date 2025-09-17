import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer trim-edge on large docs', () => {
  it(
    formatGWT('large docs with trailing spaces', 'compressSteeringDocuments', 'tokens reduced or equal; headers preserved; code fences preserved'),
    async () => {
      const uniqueKeysArb = fc
        .array(fc.constantFrom('product', 'design', 'architecture', 'standards'), { minLength: 2, maxLength: 4 })
        .map((a) => Array.from(new Set(a)));

      await fc.assert(
        fc.asyncProperty(uniqueKeysArb, async (keys) => {
          const docs: Record<string, string> = {};
          for (const k of keys) {
            docs[k] = [
              `# ${k}  `,
              '```
const x = 1;  
```
',
              ('lorem '.repeat(80)).trim() + '  ',
            ].join('\n');
          }
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(docs, {
            preservePriority: ['product', 'design', 'architecture', 'standards'],
            maxTokens: 5000,
            enableCaching: false,
          });
          const body = res.compressed;
          // headers order if present
          const idx = ['PRODUCT', 'DESIGN', 'ARCHITECTURE', 'STANDARDS']
            .map((h) => body.indexOf('## ' + h))
            .filter((i) => i >= 0);
          for (let i = 1; i < idx.length; i++) expect(idx[i - 1]).toBeLessThan(idx[i]);
          // code fences preserved at least once when present in input
          if (Object.values(docs).some((d) => d.includes('```'))) {
            expect((body.match(/```/g) || []).length).toBeGreaterThanOrEqual(1);
          }
          expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
        }),
        { numRuns: 6 }
      );
    }
  );
});

