import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer priority extreme boundary 4 (large)', () => {
  it(
    formatGWT('missing middle priority', 'compressSteeringDocuments', 'order respects present sections only'),
    async () => {
      const opt = new TokenOptimizer();
      const docs = {
        product: '# product\n' + 'lorem '.repeat(100),
        standards: '# standards\n' + 'ipsum '.repeat(80)
      } as Record<string,string>;
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 7000, enableCaching: false });
      const body = res.compressed;
      const iProd = body.indexOf('## PRODUCT');
      const iStd = body.indexOf('## STANDARDS');
      expect(iProd).toBeGreaterThanOrEqual(0);
      expect(iStd).toBeGreaterThan(iProd);
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
    }
  );
});

