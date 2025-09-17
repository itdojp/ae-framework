import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer large codeblocks preserved', () => {
  it(
    formatGWT('large code fences', 'compressSteeringDocuments', 'compressed <= original and fences remain'),
    async () => {
      await fc.assert(
        fc.asyncProperty(fc.string({ minLength: 5, maxLength: 60 }), async (s) => {
          const code = '```ts\n' + Array.from({ length: 20 }, (_, i) => `const v${i} = '${s}';`).join('\n') + '\n```';
          const content = ['# Title', s.repeat(3), code, s.repeat(2), code].join('\n');
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments({ product: content }, { maxTokens: 8000 });
          expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
          const fences = (res.compressed.match(/```/g) || []).length;
          expect(fences % 2).toBe(0);
        }),
        { numRuns: 6 }
      );
    }
  );
});

