import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import fc from 'fast-check';

describe('PBT: TokenOptimizer compression high <= medium (estimate tokens)', () => {
  it('high compression should not produce more tokens than medium', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          product: fc.string({ minLength: 300, maxLength: 1200 }),
          architecture: fc.string({ minLength: 300, maxLength: 1200 }),
          standards: fc.string({ minLength: 300, maxLength: 1200 })
        }),
        async (docs) => {
          const opt = new TokenOptimizer();
          const med = await opt.compressSteeringDocuments(docs as any, { maxTokens: 1000, compressionLevel: 'medium' });
          const high = await opt.compressSteeringDocuments(docs as any, { maxTokens: 1000, compressionLevel: 'high' });
          expect(high.stats.compressed).toBeLessThanOrEqual(med.stats.compressed);
        }
      ),
      { numRuns: 6 }
    );
  });
});

