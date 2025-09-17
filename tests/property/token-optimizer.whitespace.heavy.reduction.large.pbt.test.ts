import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer whitespace heavy reduction (large)', () => {
  it(
    formatGWT('whitespace-heavy docs', 'compressSteeringDocuments', 'tokens not increased; headers first'),
    async () => {
      const docs: Record<string,string> = {
        product: ['# product', '', ' ', ' '.repeat(1000), ('alpha '.repeat(120))].join('\n'),
        architecture: ['# architecture', ' ', ' ', ('beta '.repeat(100))].join('\n')
      };
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 12000, enableCaching: false });
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
      const body = res.compressed;
      const iProd = body.indexOf('## PRODUCT');
      const iArch = body.indexOf('## ARCHITECTURE');
      expect(iProd).toBeGreaterThanOrEqual(0);
      expect(iArch).toBeGreaterThan(iProd);
    }
  );
});

