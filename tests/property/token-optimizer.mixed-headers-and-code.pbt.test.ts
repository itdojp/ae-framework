import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer mixed headers and code', () => {
  it(
    formatGWT('docs contain headers & code', 'compressSteeringDocuments', 'compressed <= original & code fences remain'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 20, maxLength: 120 }),
          async (s) => {
            const code = '```ts\nexport const a=1\n```';
            const hdr = '## SECTION';
            const docs = {
              product: `${hdr}\n${s}\n${code}\n${s}`,
              architecture: `${hdr}\n${s}`,
              standards: `${code}\n${s}`,
            } as Record<string,string>;
            const opt = new TokenOptimizer();
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 4000, enableCaching: false });
            expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
            expect(/```[\s\S]*?```/.test(res.compressed)).toBe(true);
          }
        ),
        { numRuns: 8 }
      );
    }
  );
});

