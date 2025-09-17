import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer large mixed docs yield reduction', () => {
  it(
    formatGWT('large mixed content', 'compressSteeringDocuments', 'reductionPercentage >= 0'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 150, maxLength: 800 }),
          async (s) => {
            const opt = new TokenOptimizer();
            const docs = {
              product: `must: ${s}\n- item1\n- item2\n\n\n` + s.repeat(1),
              architecture: `should: ${s.slice(0, 200)}`,
              standards: `key: ${s.slice(0, 120)}\n\n` + '```md\n# Title\n```',
            } as Record<string,string>;
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 5000, enableCaching: false });
            expect(res.stats.reductionPercentage).toBeGreaterThanOrEqual(0);
          }
        ),
        { numRuns: 8 }
      );
    }
  );
});

