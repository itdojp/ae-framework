import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer compression ladder (low >= medium >= high)', () => {
  it(formatGWT('key-indicator heavy text', 'compress at low/medium/high', 'tokens(low) >= tokens(med) >= tokens(high)'), async () => {
    const opt = new TokenOptimizer();
    const content = [
      '# Title',
      '- must: 1',
      '- should: 2',
      '- important: 3',
      'This paragraph repeats. '.repeat(50)
    ].join('\n');
    const docs = { product: content };
    const low = await opt.compressSteeringDocuments(docs, { compressionLevel: 'low', maxTokens: 5000 });
    const med = await opt.compressSteeringDocuments(docs, { compressionLevel: 'medium', maxTokens: 5000 });
    const high = await opt.compressSteeringDocuments(docs, { compressionLevel: 'high', maxTokens: 5000 });
    expect(low.stats.compressed).toBeGreaterThanOrEqual(med.stats.compressed);
    expect(med.stats.compressed).toBeGreaterThanOrEqual(high.stats.compressed);
  });
});

