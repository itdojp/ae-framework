import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer present-only sections (large alt2)', () => {
  it(
    formatGWT('docs with product/architecture', 'compressSteeringDocuments', 'no absent sections introduced; tokens not increased'),
    async () => {
      const docs: Record<string,string> = {
        product: '# product\n' + 'alpha '.repeat(150),
        architecture: '# architecture\n' + 'beta '.repeat(150)
      };
      const opt = new TokenOptimizer();
      const { compressed, stats } = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 14000, enableCaching: false });
      expect(stats.compressed).toBeLessThanOrEqual(stats.original);
      expect(compressed.includes('## DESIGN')).toBe(false);
      expect(compressed.includes('## STANDARDS')).toBe(false);
    }
  );
});

