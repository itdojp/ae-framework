import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer cache consistency on large docs', () => {
  it(
    formatGWT('large docs', 'compress with caching on/off', 'same output & tokens reduced'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.array(fc.constantFrom('product','design','architecture','standards'), { minLength: 2, maxLength: 4 }).map(a=>Array.from(new Set(a))),
          async (keys) => {
            const docs: Record<string,string> = {};
            for (const k of keys) docs[k] = `# ${k}\n` + ('lorem '.repeat(120));
            const opt = new TokenOptimizer();
            const r1 = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 9000, enableCaching: false });
            const r2 = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 9000, enableCaching: true });
            expect(r2.compressed).toBe(r1.compressed);
            expect(r2.stats.compressed).toBeLessThanOrEqual(r2.stats.original);
          }
        ),
        { numRuns: 5 }
      );
    }
  );
});

