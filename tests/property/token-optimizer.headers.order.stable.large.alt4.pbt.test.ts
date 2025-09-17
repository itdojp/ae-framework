import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer headers order stable (large alt4)', () => {
  it(
    formatGWT('present sections product/architecture reversed input', 'compressSteeringDocuments', 'order respects preservePriority'),
    async () => {
      const opt = new TokenOptimizer();
      const docs = {
        architecture: '# architecture\n' + 'ipsum '.repeat(140),
        product: '# product\n' + 'lorem '.repeat(160)
      } as Record<string,string>;
      const { compressed, stats } = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 15000, enableCaching: false });
      expect(stats.compressed).toBeLessThanOrEqual(stats.original);
      const idxProd = compressed.indexOf('## PRODUCT');
      const idxArch = compressed.indexOf('## ARCHITECTURE');
      expect(idxProd).toBeGreaterThanOrEqual(0);
      expect(idxArch).toBeGreaterThan(idxProd);
    }
  );
});

