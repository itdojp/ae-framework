import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer preserves code blocks with high compression', () => {
  it(
    formatGWT('docs include ```code``` blocks', 'compressSteeringDocuments (high)', 'code fences remain'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 20, maxLength: 120 }),
          async (s) => {
            const opt = new TokenOptimizer();
            const code = '```ts\nconst x: number = 1;\n```';
            const docs = {
              product: `${s}\n${code}\n${s}`,
              architecture: `${s}`,
              standards: `${code}`,
            } as Record<string,string>;
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 1000, compressionLevel: 'high', enableCaching: false });
            expect(/```[\s\S]*?```/.test(res.compressed)).toBe(true);
          }
        ),
        { numRuns: 8 }
      );
    }
  );
});

