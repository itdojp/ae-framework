import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer sections order stable under random docs', () => {
  it(
    formatGWT('randomized section order', 'compressSteeringDocuments', 'headers follow preservePriority among present'),
    async () => {
      const sectionKeysArb = fc.shuffledSubarray(
        ['product', 'design', 'architecture', 'standards'],
        { minLength: 2, maxLength: 4 }
      );
      const keysWithOrderArb = sectionKeysArb.chain((keys) =>
        fc
          .shuffledSubarray(keys, { minLength: keys.length, maxLength: keys.length })
          .map((insertionOrder) => ({ keys, insertionOrder }))
      );
      const preservePriority = ['product', 'design', 'architecture', 'standards'];
      const headers = ['PRODUCT', 'DESIGN', 'ARCHITECTURE', 'STANDARDS'];

      await fc.assert(
        fc.asyncProperty(keysWithOrderArb, async ({ keys, insertionOrder }) => {
          const docs: Record<string,string> = {};
          for (const k of insertionOrder) docs[k] = `${k} content`.repeat(2);
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(docs, {
            preservePriority,
            maxTokens: 1000,
            enableCaching: false
          });
          const body = res.compressed;
          const indices = headers
            .map((h) => body.indexOf(`## ${h}`))
            .filter((i) => i >= 0);
          for (let i=1;i<indices.length;i++) expect(indices[i-1]).toBeLessThan(indices[i]);
        }),
        { numRuns: 8 }
      );
    }
  );
});
