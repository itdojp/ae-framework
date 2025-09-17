import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer priority interleaved headers (large)', () => {
  it(
    formatGWT('interleaved headers', 'compressSteeringDocuments', 'preservePriority among present (large docs)'),
    async () => {
      const uniqueKeysArb = fc
        .array(fc.constantFrom('product','design','architecture','standards'), { minLength: 2, maxLength: 4 })
        .map(a=>Array.from(new Set(a)));

      await fc.assert(
        fc.asyncProperty(uniqueKeysArb, async (keys) => {
          // Create docs with interleaved header-like lines to stress ordering
          const docs: Record<string,string> = {};
          for (const k of keys) {
            const body = [
              `# ${k}`,
              '## SUBSECTION',
              ('lorem '.repeat(150)),
              '## NOTE',
              ('ipsum '.repeat(150)),
            ].join('\n');
            docs[k] = body;
          }
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 12000, enableCaching: false });
          const body = res.compressed;
          const idx = ['PRODUCT','DESIGN','ARCHITECTURE','STANDARDS']
            .map(h=> body.indexOf('## '+h))
            .filter(i=>i>=0);
          for (let i=1;i<idx.length;i++) expect(idx[i-1]).toBeLessThan(idx[i]);
          expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
        }),
        { numRuns: 5 }
      );
    }
  );
});

