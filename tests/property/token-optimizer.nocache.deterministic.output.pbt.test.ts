import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer deterministic output without cache', () => {
  it(
    formatGWT('same docs/options twice', 'compressSteeringDocuments (enableCaching=false)', 'outputs are identical'),
    async () => {
      await fc.assert(
        fc.asyncProperty(fc.string({ minLength: 5, maxLength: 80 }), async (s) => {
          const docs = { product: `P ${s}`, design: `D ${s.slice(0, 10)}` } as Record<string, string>;
          const opt = new TokenOptimizer();
          const opts = { maxTokens: 500, enableCaching: false } as const;
          const a = await opt.compressSteeringDocuments(docs, opts);
          const b = await opt.compressSteeringDocuments(docs, opts);
          expect(a.compressed).toBe(b.compressed);
          expect(a.stats.compressed).toBe(b.stats.compressed);
        }),
        { numRuns: 8 }
      );
    }
  );
});

