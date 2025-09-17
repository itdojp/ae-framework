import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('TokenOptimizer compressionLevel effect', () => {
  it('high compression produces tokens <= low compression for key-indicator content', async () => {
    const opt = new TokenOptimizer();
    const content = [
      '# Title\n',
      '- must: include security checks.\n',
      '- should: add logging.\n',
      '- important: performance constraints.\n',
      'This paragraph repeats repeats repeats. '.repeat(20),
    ].join('');
    const docs = { product: content };
    const low = await opt.compressSteeringDocuments(docs, { compressionLevel: 'low', maxTokens: 2000 });
    const high = await opt.compressSteeringDocuments(docs, { compressionLevel: 'high', maxTokens: 2000 });
    expect(high.stats.compressed).toBeLessThanOrEqual(low.stats.compressed);
    expect(typeof high.compressed).toBe('string');
  });
});

