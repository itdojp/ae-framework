import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer truncate boundary (fast)', () => {
  it(formatGWT('large docs', 'compress with small maxTokens', 'tokens <= limit and ends sensibly'), async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          repeats: fc.integer({ min: 10, max: 60 }),
          maxTokens: fc.integer({ min: 120, max: 300 })
        }),
        async ({ repeats, maxTokens }) => {
          const opt = new TokenOptimizer();
          const docs = {
            product: 'must: goals. '.repeat(repeats),
            architecture: 'should: structure. '.repeat(repeats),
            standards: 'key: style. '.repeat(repeats)
          } as Record<string,string>;
          const { compressed, stats } = await opt.compressSteeringDocuments(docs, { maxTokens });
          expect(stats.compressed).toBeLessThanOrEqual(maxTokens);
          const tail = compressed.trim().slice(-20);
          // either truncated sentinel or a sensible sentence end
          expect(tail.includes('[...truncated]') || /[.!?]$/.test(compressed.trim())).toBe(true);
        }
      ),
      { numRuns: 12 }
    );
  });
});

