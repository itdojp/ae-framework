import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer present-only sections keep order (idempotent)', () => {
  it(
    formatGWT('present-only order', 'compressSteeringDocuments', 'preservePriority order among present is stable'),
    async () => {
      const uniqueKeysArb = fc
        .array(fc.constantFrom('product', 'design', 'architecture', 'standards'), { minLength: 2, maxLength: 4 })
        .map((a) => Array.from(new Set(a)));
      await fc.assert(
        fc.asyncProperty(uniqueKeysArb, async (keys) => {
          const docs: Record<string, string> = {};
          for (const k of keys) docs[k] = `# ${k}\n` + ('lorem '.repeat(40));
          const opt = new TokenOptimizer();
          const res1 = await opt.compressSteeringDocuments(docs, { preservePriority: ['product', 'design', 'architecture', 'standards'], maxTokens: 5000, enableCaching: false });
          const res2 = await opt.compressSteeringDocuments(docs, { preservePriority: ['product', 'design', 'architecture', 'standards'], maxTokens: 5000, enableCaching: false });
          const body1 = res1.compressed;
          const body2 = res2.compressed;
          expect(body1).toBe(body2);
        }),
        { numRuns: 6 }
      );
    }
  );
});

