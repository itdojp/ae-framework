import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer duplicate paragraphs deduplication', () => {
  it(
    formatGWT('multiple repeated paragraphs', 'compressSteeringDocuments', 'compressed tokens do not exceed original'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 20, maxLength: 100 }),
          async (s) => {
            const opt = new TokenOptimizer();
            const para = `${s}. ${s}! ${s}?`;
            const docs = {
              product: `${para}\n\n${para}`,
              architecture: `${para}\n\n${para}`,
              standards: `${para}`,
            } as Record<string,string>;
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 4000, enableCaching: false });
            expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
          }
        ),
        { numRuns: 10 }
      );
    }
  );
});

