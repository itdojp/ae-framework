import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer large docs with many headers', () => {
  it(
    formatGWT('large docs with many headers', 'compressSteeringDocuments', 'compressed tokens <= original'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 50, maxLength: 200 }),
          async (s) => {
            const many = Array.from({ length: 10 }, (_, i) => `## H${i+1}\n${s}`).join('\n');
            const docs = {
              product: many,
              architecture: many,
              standards: many,
            } as Record<string,string>;
            const opt = new TokenOptimizer();
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 8000, enableCaching: false });
            expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
          }
        ),
        { numRuns: 6 }
      );
    }
  );
});

