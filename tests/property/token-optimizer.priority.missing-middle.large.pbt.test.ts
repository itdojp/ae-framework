import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer priority with missing middle sections (large)', () => {
  it(
    formatGWT('missing middle sections', 'compressSteeringDocuments', 'headers in preservePriority among present'),
    async () => {
      const docs: Record<string,string> = {
        product: '# product\n' + 'lorem '.repeat(120),
        standards: '# standards\n' + 'ipsum '.repeat(120)
      };
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 9000, enableCaching: false });
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
      // Since only product and standards exist, product must come before standards
      expect(res.compressed.indexOf('## PRODUCT')).toBeLessThan(res.compressed.indexOf('## STANDARDS'));
    }
  );
});

