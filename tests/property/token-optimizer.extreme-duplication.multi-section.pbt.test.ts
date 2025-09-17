import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer extreme duplication across sections', () => {
  it(
    formatGWT('multi-section repeated sentences', 'compressSteeringDocuments', 'compressed tokens <= original'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 10, maxLength: 60 }),
          async (s) => {
            const para = `${s}. ${s}! ${s}?`;
            const docs = {
              product: `${para} ${para}`,
              architecture: `${para}`,
              standards: `${para} ${para}`,
            } as Record<string,string>;
            const opt = new TokenOptimizer();
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 5000, enableCaching: false });
            expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
          }
        ),
        { numRuns: 10 }
      );
    }
  );
});

