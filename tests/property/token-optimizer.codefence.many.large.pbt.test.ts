import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer many code fences in large inputs', () => {
  it(
    formatGWT('large docs with many code fences', 'compressSteeringDocuments', 'preserve at least one fence; tokens reduced or equal'),
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
              '```
code A
```
',
              '```
code B
```
',
              '```
code C
```
',
              ('lorem '.repeat(100)),
            ].join('\n');
          }
          const opt = new TokenOptimizer();
          const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product', 'design', 'architecture', 'standards'], maxTokens: 8000, enableCaching: false });
          const body = res.compressed;
          // At least one code fence should remain
          expect((body.match(/```/g) || []).length).toBeGreaterThanOrEqual(1);
          expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
        }),
        { numRuns: 5 }
      );
    }
  );
});

