import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: no sentinel when not truncated', () => {
  it(formatGWT('small docs', 'compress with large maxTokens', 'no [...truncated] sentinel appears'), async () => {
    const opt = new TokenOptimizer();
    const docs = {
      product: 'must: goals.',
      architecture: 'should: structure.',
      standards: 'key: style.'
    } as Record<string,string>;
    const { compressed, stats } = await opt.compressSteeringDocuments(docs, { maxTokens: 5000 });
    expect(stats.compressed).toBeLessThanOrEqual(5000);
    expect(compressed.includes('[...truncated]')).toBe(false);
  });
});

