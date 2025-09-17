import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer priority random subsets (large)', () => {
  it(
    formatGWT('random subsets', 'compressSteeringDocuments twice', 'idempotent ordering & tokens reduced'),
    async () => {
      const uniqueKeysArb = fc
        .array(fc.constantFrom('product','design','architecture','standards'), { minLength: 1, maxLength: 4 })
        .map(a=>Array.from(new Set(a)));
      await fc.assert(
        fc.asyncProperty(uniqueKeysArb, async (keys) => {
          const docs: Record<string, string> = {};
          for (const k of keys) docs[k] = `# ${k}\n` + ('ipsum '.repeat(80));
          const opt = new TokenOptimizer();
          const r1 = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 8000, enableCaching: false });
          const r2 = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 8000, enableCaching: false });
          expect(r1.compressed).toBe(r2.compressed);
          expect(r1.stats.compressed).toBeLessThanOrEqual(r1.stats.original);
        }),
        { numRuns: 6 }
      );
    }
  );
});

