import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer headers order stable (large alt3)', () => {
  it(
    formatGWT('present sections product/standards only', 'compressSteeringDocuments', 'order respects preservePriority when middle missing'),
    async () => {
      const opt = new TokenOptimizer();
      const docs = {
        standards: '# standards\n' + 'gamma '.repeat(90),
        product: '# product\n' + 'alpha '.repeat(120)
      } as Record<string,string>;
      const { compressed, stats } = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 14000, enableCaching: false });
      expect(stats.compressed).toBeLessThanOrEqual(stats.original);
      const idxProd = compressed.indexOf('## PRODUCT');
      const idxStd = compressed.indexOf('## STANDARDS');
      expect(idxProd).toBeGreaterThanOrEqual(0);
      expect(idxStd).toBeGreaterThan(idxProd);
    }
  );
});

