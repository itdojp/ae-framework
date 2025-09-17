import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer large data preserves order by priority', () => {
  it(
    formatGWT('large randomized docs', 'compressSteeringDocuments', 'headers appear in priority order among present'),
    async () => {
      await fc.assert(
        fc.asyncProperty(fc.array(fc.constantFrom('product','design','architecture','standards'), {minLength:2, maxLength:4}).map(a=>Array.from(new Set(a))), async (keys) => {
          const docs: Record<string,string> = {};
          for (const k of keys) docs[k] = (k+': ').repeat(200);
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 5000, enableCaching: false });
          const body = res.compressed;
          const idx = ['PRODUCT','DESIGN','ARCHITECTURE','STANDARDS'].map(h=> body.indexOf('## '+h)).filter(i=>i>=0);
          for (let i=1;i<idx.length;i++) expect(idx[i-1]).toBeLessThan(idx[i]);
        }),
        { numRuns: 6 }
      );
    }
  );
});

