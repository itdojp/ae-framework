import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer preservePriority random + missing top', () => {
  it(
    formatGWT('random docs, missing top priority', 'compressSteeringDocuments', 'first section is next in priority'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 5, maxLength: 40 }),
          async (s) => {
            const base = { product: `p: ${s}`, architecture: `a: ${s}` } as Record<string,string>;
            const entries = Object.entries(base);
            entries.sort(() => Math.random() - 0.5);
            const docs = Object.fromEntries(entries) as Record<string,string>;
            const opt = new TokenOptimizer();
            const res = await opt.compressSteeringDocuments(docs, {
              preservePriority: ['standards','product','architecture'],
              maxTokens: 80,
              enableCaching: false,
            });
            if (res.compressed.trim().length > 0) {
              expect(res.compressed.trim().startsWith('## PRODUCT')).toBe(true);
            }
          }
        ),
        { numRuns: 12 }
      );
    }
  );
});

