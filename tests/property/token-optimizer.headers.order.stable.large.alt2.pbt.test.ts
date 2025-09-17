import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer headers order stable (large alt2)', () => {
  it(
    formatGWT('present sections product/architecture/standards', 'compressSteeringDocuments', 'order respects preservePriority'),
    async () => {
      const opt = new TokenOptimizer();
      const docs = {
        architecture: '# architecture\n' + 'ipsum '.repeat(120),
        product: '# product\n' + 'lorem '.repeat(140),
        standards: '# standards\n' + 'dolor '.repeat(100)
      } as Record<string,string>;
      const { compressed, stats } = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 15000, enableCaching: false });
      expect(stats.compressed).toBeLessThanOrEqual(stats.original);
      const idxProd = compressed.indexOf('## PRODUCT');
      const idxArch = compressed.indexOf('## ARCHITECTURE');
      const idxStd = compressed.indexOf('## STANDARDS');
      expect(idxProd).toBeGreaterThanOrEqual(0);
      expect(idxArch).toBeGreaterThan(idxProd);
      expect(idxStd).toBeGreaterThan(idxArch);
    }
  );
});

