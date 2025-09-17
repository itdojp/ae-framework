import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer priority extreme boundary (large)', () => {
  it(
    formatGWT('extreme subsets', 'compressSteeringDocuments', 'headers follow preservePriority among present'),
    async () => {
      const subsets = [
        ['product'],
        ['design'],
        ['architecture'],
        ['standards'],
        ['product','standards'],
        ['design','architecture']
      ];
      await fc.assert(
        fc.asyncProperty(fc.constantFrom(...subsets), async (keys) => {
          const docs: Record<string, string> = {};
          for (const k of keys) docs[k] = `# ${k}\n` + ('lorem '.repeat(100));
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 9000, enableCaching: false });
          const body = res.compressed;
          const idx = ['PRODUCT','DESIGN','ARCHITECTURE','STANDARDS'].map(h=> body.indexOf('## '+h)).filter(i=>i>=0);
          for (let i=1;i<idx.length;i++) expect(idx[i-1]).toBeLessThan(idx[i]);
          expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
        }),
        { numRuns: 6 }
      );
    }
  );
});

