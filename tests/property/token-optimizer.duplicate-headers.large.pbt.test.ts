import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer duplicate headers on large inputs', () => {
  it(
    formatGWT('large docs with duplicate headers', 'compressSteeringDocuments', 'dedup headers; tokens reduced or equal'),
    async () => {
      const uniqueKeysArb = fc
        .array(fc.constantFrom('product', 'design', 'architecture', 'standards'), { minLength: 2, maxLength: 4 })
        .map((a) => Array.from(new Set(a)));

      await fc.assert(
        fc.asyncProperty(uniqueKeysArb, async (keys) => {
          const docs: Record<string, string> = {};
          for (const k of keys) {
            docs[k] = [
              `# ${k}`,
              `# ${k}`,
              `# ${k}`,
              ('lorem '.repeat(120)),
            ].join('\n');
          }
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product', 'design', 'architecture', 'standards'], maxTokens: 8000, enableCaching: false });
          const body = res.compressed;
          // Expect at most two repeated lines of the same header text in compressed output
          expect((body.match(/^#\s+(product|design|architecture|standards)$/gmi) || []).length).toBeLessThanOrEqual(2 * keys.length);
          expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
        }),
        { numRuns: 5 }
      );
    }
  );
});

