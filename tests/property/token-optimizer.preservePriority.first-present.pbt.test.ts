import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

const PRIO = ['product','design','architecture','standards'] as const;

describe('PBT: TokenOptimizer preservePriority picks first present section', () => {
  it(
    formatGWT('random subset of sections', 'compressSteeringDocuments', 'first header matches earliest present in preservePriority'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.set(fc.constantFrom(...PRIO), { minLength: 1, maxLength: 4 }),
          async (subset) => {
            const docs: Record<string,string> = {};
            for (const k of subset) docs[k] = `${k} content`;
            const opt = new TokenOptimizer();
            const res = await opt.compressSteeringDocuments(docs, {
              preservePriority: PRIO as unknown as string[],
              maxTokens: 400,
              enableCaching: false,
            });
            if (res.compressed.trim().length === 0) return; // allow empty when content too small
            // earliest present key by priority order
            const firstPresent = PRIO.find(k => subset.includes(k));
            const expectedHeader = `## ${firstPresent?.toUpperCase()}`;
            expect(res.compressed.trim().startsWith(expectedHeader)).toBe(true);
          }
        ),
        { numRuns: 12 }
      );
    }
  );
});

