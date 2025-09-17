import { describe, test, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer.js';

describe('TokenOptimizer — maxTokens monotonicity', () => {
  test('compressed tokens do not increase when maxTokens decreases', async () => {
    const optimizer = new TokenOptimizer();
    const docs = {
      product: 'Important: core goals. '.repeat(200),
      architecture: '# Comp\n' + 'Service A/B/C. '.repeat(200),
      standards: '- rule1\n- rule2\n'.repeat(100),
    } as Record<string, string>;

    const resHigh = await optimizer.compressSteeringDocuments(docs, { maxTokens: 2000, compressionLevel: 'medium' });
    const resLow = await optimizer.compressSteeringDocuments(docs, { maxTokens: 800, compressionLevel: 'medium' });

    expect(resLow.stats.compressed).toBeLessThanOrEqual(resHigh.stats.compressed);
  });
});

