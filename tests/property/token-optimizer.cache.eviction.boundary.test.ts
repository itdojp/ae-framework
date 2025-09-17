import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('TokenOptimizer: cache eviction boundary', () => {
  it('cache size never exceeds maxSize under repeated compressions', async () => {
    const opt = new TokenOptimizer();
    // Generate more than internal CACHE_SIZE (=100)
    const N = 120;
    for (let i = 0; i < N; i++) {
      const docs = { product: `p-${i}`, architecture: `a-${i}`, standards: `s-${i}` } as any;
      await opt.compressSteeringDocuments(docs, { maxTokens: 200, compressionLevel: 'low', enableCaching: true });
    }
    const stats = opt.getCacheStats();
    expect(stats.size).toBeLessThanOrEqual(stats.maxSize);
  });
});

