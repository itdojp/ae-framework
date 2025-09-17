import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer large docs smoke (code blocks preserved)', () => {
  it(
    formatGWT('large docs with code fences', 'compressSteeringDocuments', 'compressed <= original and code fences intact'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 200, maxLength: 1000 }),
          async (s) => {
            const opt = new TokenOptimizer();
            const code = '```js\nfunction test(){ return 42 }\n```';
            const docs = {
              product: `${s}\n${code}`,
              architecture: `${s.slice(0, Math.floor(s.length/2))}`,
              standards: `${code}\n${s.slice(0, 120)}`,
            } as Record<string, string>;
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 5000, enableCaching: false });
            expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
            // Code fence should remain
            expect(/```[\s\S]*?```/.test(res.compressed)).toBe(true);
          }
        ),
        { numRuns: 8 }
      );
    }
  );
});

