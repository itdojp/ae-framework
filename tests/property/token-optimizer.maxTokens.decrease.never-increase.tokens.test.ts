import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: lowering maxTokens never increases compressed tokens', () => {
  it(
    formatGWT('same docs', 'compress at maxTokens=800 then 400', 'compressed tokens(400) <= tokens(800)'),
    async () => {
      const docs = {
        product: 'P '.repeat(100),
        architecture: 'A '.repeat(80),
        standards: 'S '.repeat(60),
      } as Record<string,string>;
      const opt = new TokenOptimizer();
      const hi = await opt.compressSteeringDocuments(docs, { maxTokens: 800 });
      const lo = await opt.compressSteeringDocuments(docs, { maxTokens: 400 });
      expect(lo.stats.compressed).toBeLessThanOrEqual(hi.stats.compressed);
    }
  );
});

