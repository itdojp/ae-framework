import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

function countFences(s: string): number {
  const m = s.match(/```[\s\s]*?```/g);
  return m ? m.length : 0;
}

describe('PBT: TokenOptimizer code fence count is preserved or present', () => {
  it(
    formatGWT('docs with N code fences', 'compressSteeringDocuments', 'output contains >=1 fence when input has >=1'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.integer({ min: 1, max: 3 }),
          fc.string({ minLength: 10, maxLength: 60 }),
          async (n, s) => {
            const fence = '```ts\nconst n=1\n```';
            const fences = Array.from({ length: n }, () => fence).join('\n');
            const docs = {
              product: `${s}\n${fences}`,
              architecture: `${s}`,
              standards: `${fences}`,
            } as Record<string,string>;
            const opt = new TokenOptimizer();
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 6000, enableCaching: false });
            const inCount = countFences(`${docs.product}\n${docs.architecture}\n${docs.standards}`);
            const outCount = countFences(res.compressed);
            expect(outCount).toBeGreaterThanOrEqual(Math.min(1, inCount));
          }
        ),
        { numRuns: 6 }
      );
    }
  );
});

