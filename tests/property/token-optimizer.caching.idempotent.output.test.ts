import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: caching produces idempotent output', () => {
  it(formatGWT('same docs/options', 'compress twice with caching', 'identical compressed output and tokens'), async () => {
    const opt = new TokenOptimizer();
    const docs = {
      product: 'must: goals. '.repeat(20),
      architecture: 'should: structure. '.repeat(10),
      standards: 'key: style. '.repeat(5)
    } as Record<string,string>;
    const opts = { maxTokens: 500, enableCaching: true as const };
    const a = await opt.compressSteeringDocuments(docs, opts);
    const b = await opt.compressSteeringDocuments(docs, opts);
    expect(a.compressed).toBe(b.compressed);
    expect(a.stats.compressed).toBe(b.stats.compressed);
  });
});

