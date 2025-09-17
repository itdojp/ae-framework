import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer priority extreme boundary 3 (large)', () => {
  it(
    formatGWT('multi-section extremes', 'compressSteeringDocuments', 'preservePriority order and token monotonicity'),
    async () => {
      const opt = new TokenOptimizer();
      const docs = {
        product: '# product\n' + 'lorem '.repeat(120),
        architecture: '# architecture\n' + 'ipsum '.repeat(110),
        standards: '# standards\n' + 'dolor '.repeat(100)
      } as Record<string,string>;
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 8000, enableCaching: false });
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
      const body = res.compressed;
      const iProd = body.indexOf('## PRODUCT');
      const iArch = body.indexOf('## ARCHITECTURE');
      const iStd = body.indexOf('## STANDARDS');
      expect(iProd).toBeGreaterThanOrEqual(0);
      expect(iArch).toBeGreaterThan(iProd);
      expect(iStd).toBeGreaterThan(iArch);
    }
  );
});

