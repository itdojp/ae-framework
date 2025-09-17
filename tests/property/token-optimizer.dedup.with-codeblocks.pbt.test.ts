import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer deduplication with codeblocks preserved', () => {
  it(
    formatGWT('repeated paragraphs + codeblocks', 'compressSteeringDocuments', 'compressed <= original and code fences remain'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 10, maxLength: 60 }),
          async (s) => {
            const para = `${s}. ${s}! ${s}?`;
            const code = '```js\nfunction x(){return 1}\n```';
            const docs = {
              product: `${para}\n${code}\n${para}`,
              architecture: `${para}`,
              standards: `${code}`,
            } as Record<string,string>;
            const opt = new TokenOptimizer();
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 3000, enableCaching: false });
            expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
            expect(/```[\s\S]*?```/.test(res.compressed)).toBe(true);
          }
        ),
        { numRuns: 8 }
      );
    }
  );
});

