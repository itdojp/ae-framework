import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer sections order stable under random docs', () => {
  it(
    formatGWT('randomized section order', 'compressSteeringDocuments', 'headers follow preservePriority among present'),
    async () => {
      await fc.assert(
        fc.asyncProperty(fc.array(fc.constantFrom('product','design','architecture','standards'), {minLength:2, maxLength:4}).map(arr=>Array.from(new Set(arr))), async (keys) => {
          const docs: Record<string,string> = {};
          for (const k of keys) docs[k] = `${k} content`.repeat(2);
          // randomize insertion order
          const shuffled = [...keys].sort(()=>Math.random()-0.5);
          const randomizedDocs: Record<string,string> = {};
          for (const k of shuffled) randomizedDocs[k] = docs[k];
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(randomizedDocs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 1000, enableCaching: false });
          const body = res.compressed;
          const indices = ['PRODUCT','DESIGN','ARCHITECTURE','STANDARDS'].map(h=> body.indexOf(`## ${h}`)).filter(i=>i>=0);
          for (let i=1;i<indices.length;i++) expect(indices[i-1]).toBeLessThan(indices[i]);
        }),
        { numRuns: 8 }
      );
    }
  );
});

