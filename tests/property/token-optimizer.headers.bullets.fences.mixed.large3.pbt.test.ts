import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer headers+bullets+fences mixed (large3)', () => {
  it(
    formatGWT('large mixed content', 'compressSteeringDocuments', 'at least one code fence kept; headers lead; tokens reduced'),
    async () => {
      const docs: Record<string,string> = {
        product: [
          '# product',
          '```ts',
          'const x = 1;',
          '```',
          '- a',
          '- a',
          ('alpha '.repeat(140))
        ].join('\n'),
        architecture: [
          '# architecture',
          '- b',
          '- b',
          ('beta '.repeat(120))
        ].join('\n'),
        standards: [
          '# standards',
          ('gamma '.repeat(100))
        ].join('\n')
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

