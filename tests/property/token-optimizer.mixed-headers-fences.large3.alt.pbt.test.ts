import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer mixed headers+fences large3 (alt)', () => {
  it(
    formatGWT('mixed alt', 'compressSteeringDocuments', 'one code fence kept; headers lead; tokens reduced'),
    async () => {
      const docs: Record<string,string> = {
        product: ['# product','```','sample','```',('a '.repeat(120))].join('\n'),
        architecture: ['# architecture',('b '.repeat(110))].join('\n'),
        standards: ['# standards','- k','- k',('c '.repeat(90))].join('\n'),
      };
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 10000, enableCaching: false });
      const body = res.compressed;
      expect((body.match(/```/g) || []).length).toBeGreaterThanOrEqual(1);
      const iProd = body.indexOf('## PRODUCT');
      const iArch = body.indexOf('## ARCHITECTURE');
      const iStd = body.indexOf('## STANDARDS');
      expect(iProd).toBeGreaterThanOrEqual(0);
      expect(iArch).toBeGreaterThan(iProd);
      expect(iStd).toBeGreaterThan(iArch);
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
    }
  );
});

