import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer compression alternative content', () => {
  it(
    formatGWT('mixed headers/code/paragraphs', 'compression level comparison', 'low ≥ medium ≥ high by tokens'),
    async () => {
      await fc.assert(
        fc.asyncProperty(fc.array(fc.string({ minLength: 0, maxLength: 50 }), { minLength: 3, maxLength: 6 }), async (arr) => {
          const opt = new TokenOptimizer();
          const content = [
            `# ${arr[0] || 'A'}`,
            '```ts',
            `const x = ${JSON.stringify(arr[1] || 'x')};`,
            '```',
            `- ${arr[2] || 'b'}`,
            (arr[3] || 'para one'),
            (arr[4] || 'para two'),
          ].join('\n');
          const docs = { product: content } as Record<string, string>;
          const L = await opt.compressSteeringDocuments(docs, { compressionLevel: 'low', maxTokens: 5000 });
          const M = await opt.compressSteeringDocuments(docs, { compressionLevel: 'medium', maxTokens: 5000 });
          const H = await opt.compressSteeringDocuments(docs, { compressionLevel: 'high', maxTokens: 5000 });
          const tolerance = 1; // heuristic estimate rounding can differ by a single token
          expect(L.stats.compressed + tolerance).toBeGreaterThanOrEqual(M.stats.compressed);
          expect(M.stats.compressed + tolerance).toBeGreaterThanOrEqual(H.stats.compressed);
          expect(L.stats.compressed + tolerance).toBeGreaterThanOrEqual(H.stats.compressed);
        }),
        { numRuns: 8 }
      );
    }
  );
});
