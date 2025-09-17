import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer preservePriority random order', () => {
  it(
    formatGWT('docs in random order', 'compress with custom preservePriority', 'first section respects priority'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 5, maxLength: 40 }),
          async (s) => {
            const docsBase = {
              product: `p: ${s}`,
              architecture: `a: ${s}`,
              standards: `s: ${s}`,
            } as Record<string,string>;
            const entries = Object.entries(docsBase);
            entries.sort(() => Math.random() - 0.5);
            const docs = Object.fromEntries(entries) as Record<string,string>;
            const opt = new TokenOptimizer();
            const res = await opt.compressSteeringDocuments(docs, {
              preservePriority: ['standards','product','architecture'],
              maxTokens: 80,
              enableCaching: false,
            });
            if (res.compressed.trim().length > 0) {
              expect(res.compressed.trim().startsWith('## STANDARDS')).toBe(true);
            }
          }
        ),
        { numRuns: 12 }
      );
    }
  );
});

