import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer dedup never increases tokens', () => {
  it(
    formatGWT('docs with duplicated paragraphs', 'compressSteeringDocuments', 'compressed tokens <= original tokens'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.array(fc.string({ minLength: 5, maxLength: 60 }), { minLength: 3, maxLength: 6 }),
          async (arr) => {
            const para = (i: number) => `para ${i}: ${arr[i % arr.length]}`;
            const content = [
              '# Title',
              para(0),
              para(1),
              para(0), // duplicate
              '```ts',
              'const a = 1;',
              '```',
              para(2),
              para(1), // duplicate
            ].join('\n');
            const opt = new TokenOptimizer();
            const { stats } = await opt.compressSteeringDocuments({ product: content }, { maxTokens: 5000 });
            expect(stats.compressed).toBeLessThanOrEqual(stats.original);
          }
        ),
        { numRuns: 8 }
      );
    }
  );
});

