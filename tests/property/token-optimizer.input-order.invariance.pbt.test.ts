import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer input order invariance', () => {
  it(
    formatGWT('same docs content with different input order', 'compressSteeringDocuments', 'compressed output is identical'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.record({
            product: fc.string({ minLength: 10, maxLength: 100 }).map((s) => `Product: ${s}`),
            architecture: fc.string({ minLength: 5, maxLength: 80 }).map((s) => `Arch: ${s}`),
            standards: fc.string({ minLength: 5, maxLength: 80 }).map((s) => `Std: ${s}`),
          }),
          async (docs) => {
            const opt = new TokenOptimizer();
            // compress with original order (object literal order)
            const a = await opt.compressSteeringDocuments(docs, { maxTokens: 5000, enableCaching: false });
            // build a differently ordered object with same contents
            const entries = Object.entries(docs);
            const reversed = Object.fromEntries(entries.reverse());
            const b = await opt.compressSteeringDocuments(reversed as Record<string,string>, { maxTokens: 5000, enableCaching: false });
            expect(a.compressed).toBe(b.compressed);
          }
        ),
        { numRuns: 20 }
      );
    }
  );
});

