import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer empty sections produce zero or minimal output', () => {
  it(
    formatGWT('empty docs', 'compressSteeringDocuments', 'outputs minimal content (<= input tokens)'),
    async () => {
      const opt = new TokenOptimizer();
      const docs: Record<string, string> = { product: '', design: '', architecture: '', standards: '' };
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product', 'design', 'architecture', 'standards'], maxTokens: 1000, enableCaching: false });
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
      // Body should be small; at least not larger than a few headers
      expect(res.compressed.length).toBeLessThanOrEqual(200);
    }
  );
});

