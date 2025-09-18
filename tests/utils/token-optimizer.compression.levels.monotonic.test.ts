import { describe, test, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer.js';

describe('TokenOptimizer — compression levels monotonicity', () => {
  test('high <= medium <= low in compressed tokens', async () => {
    const optimizer = new TokenOptimizer();
    const docs = {
      product: 'Important: keep. '.repeat(300),
      standards: '- rule A\n- rule B\n'.repeat(150),
      architecture: '# Section\nDetails. '.repeat(200)
    } as Record<string, string>;

    const low = await optimizer.compressSteeringDocuments(docs, { compressionLevel: 'low', maxTokens: 4000 });
    const med = await optimizer.compressSteeringDocuments(docs, { compressionLevel: 'medium', maxTokens: 4000 });
    const high = await optimizer.compressSteeringDocuments(docs, { compressionLevel: 'high', maxTokens: 4000 });

    expect(med.stats.compressed).toBeLessThanOrEqual(low.stats.compressed);
    expect(high.stats.compressed).toBeLessThanOrEqual(med.stats.compressed);
  });
});

