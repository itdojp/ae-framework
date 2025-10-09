import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import fc from 'fast-check';

describe('PBT: TokenOptimizer compression medium <= low (estimate tokens)', () => {
  it('medium compression should not produce more tokens than low', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          product: fc.string({ minLength: 200, maxLength: 800 }),
          architecture: fc.string({ minLength: 200, maxLength: 800 }),
          standards: fc.string({ minLength: 200, maxLength: 800 })
        }),
        async (docs) => {
          const opt = new TokenOptimizer();
          const low = await opt.compressSteeringDocuments(docs as any, { maxTokens: 1000, compressionLevel: 'low' });
          const med = await opt.compressSteeringDocuments(docs as any, { maxTokens: 1000, compressionLevel: 'medium' });
          expect(med.stats.compressed).toBeLessThanOrEqual(low.stats.compressed + 2);
        }
      ),
      { numRuns: 6 }
    );
  });
});

