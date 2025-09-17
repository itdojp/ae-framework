import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer large docs with mixed headers and code', () => {
  it(
    formatGWT('mixed headers & code', 'compressSteeringDocuments', 'compressed <= original & code fences remain'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 60, maxLength: 240 }),
          async (s) => {
            const code1 = '```ts\nexport const X=1\n```';
            const code2 = '```js\nfunction f(){return 2}\n```';
            const hdrs = Array.from({ length: 6 }, (_, i) => `## H${i+1} ${s}`).join('\n');
            const docs = {
              product: `${hdrs}\n${code1}`,
              architecture: `${s}\n${code2}`,
              standards: `${code1}\n${code2}`,
            } as Record<string,string>;
            const opt = new TokenOptimizer();
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 9000, enableCaching: false });
            expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
            expect(/```[\s\S]*?```/.test(res.compressed)).toBe(true);
          }
        ),
        { numRuns: 6 }
      );
    }
  );
});

