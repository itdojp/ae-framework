import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('TokenOptimizer cache boundary', () => {
  it('does not grow beyond configured CACHE_SIZE', async () => {
    const opt = new TokenOptimizer();
    const base = { a: 'x' } as Record<string, string>;
    // Fill cache past its size
    for (let i = 0; i < 120; i++) {
      const docs = { ...base, [`k${i}`]: 'v'.repeat(10 + (i % 5)) } as Record<string, string>;
      await opt.compressSteeringDocuments(docs, { enableCaching: true });
    }
    const stats = opt.getCacheStats();
    expect(stats.size).toBeLessThanOrEqual(stats.maxSize);
  });
});

