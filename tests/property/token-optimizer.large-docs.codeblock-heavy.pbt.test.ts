import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer large docs codeblock-heavy', () => {
  it(
    formatGWT('large docs with many code fences', 'compressSteeringDocuments', 'compressed <= original and fences remain'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 50, maxLength: 200 }),
          async (s) => {
            const code = '```md\n# title\n```';
            const many = Array.from({ length: 5 }, () => `${s}\n${code}`).join('\n');
            const docs = { product: many, architecture: many, standards: many } as Record<string,string>;
            const opt = new TokenOptimizer();
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 8000, enableCaching: false });
            expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
            expect(/```[\s\S]*?```/.test(res.compressed)).toBe(true);
          }
        ),
        { numRuns: 6 }
      );
    }
  );
});

