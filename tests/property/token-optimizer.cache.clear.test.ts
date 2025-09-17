import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('TokenOptimizer: cache clear resets size', () => {
  it('clearCache resets cache size to 0', async () => {
    const opt = new TokenOptimizer();
    await opt.compressSteeringDocuments({ product: 'a', architecture: 'b', standards: 'c' } as any, { enableCaching: true });
    let stats = opt.getCacheStats();
    expect(stats.size).toBeGreaterThanOrEqual(0);
    opt.clearCache();
    stats = opt.getCacheStats();
    expect(stats.size).toBe(0);
  });
});

