import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer mixed headers and bullets (large)', () => {
  it(
    formatGWT('mixed headers/bullets', 'compressSteeringDocuments', 'headers first; bullets dedup; tokens reduced'),
    async () => {
      const uniqueKeysArb = fc
        .array(fc.constantFrom('product','design','architecture','standards'), { minLength: 2, maxLength: 4 })
        .map(a=>Array.from(new Set(a)));
      await fc.assert(
        fc.asyncProperty(uniqueKeysArb, async (keys) => {
          const docs: Record<string, string> = {};
          for (const k of keys) {
            docs[k] = [
              `# ${k}`,
              '- x',
              '- y',
              '- x',
              ('lorem '.repeat(120)),
            ].join('\n');
          }
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 9000, enableCaching: false });
          const body = res.compressed;
          const idx = ['PRODUCT','DESIGN','ARCHITECTURE','STANDARDS'].map(h=> body.indexOf('## '+h)).filter(i=>i>=0);
          for (let i=1;i<idx.length;i++) expect(idx[i-1]).toBeLessThan(idx[i]);
          expect((body.match(/^-[ ](x|y)$/gmi) || []).length).toBeLessThanOrEqual(2*keys.length);
          expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
        }),
        { numRuns: 6 }
      );
    }
  );
});

