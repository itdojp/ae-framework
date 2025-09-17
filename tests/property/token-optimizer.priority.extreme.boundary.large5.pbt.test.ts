import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer priority extreme boundary (large5)', () => {
  it(
    formatGWT('priority extreme', 'compress large mixed docs at extreme boundary', 'priority order preserved; tokens non-increasing'),
    async () => {
      const product = ['# product', 'A'.repeat(4000), '```js', 'console.log(1)', '```'].join('\n');
      const architecture = ['# architecture', 'B'.repeat(3000)].join('\n');
      const standards = ['# standards', 'C'.repeat(2000), '```ts', 'const y: number = 2;', '```'].join('\n');
      const docs: Record<string,string> = { product, architecture, standards };
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, {
        preservePriority: ['product','architecture','standards'],
        maxTokens: 6000,
        compressionLevel: 'high',
        enableCaching: false
      });
      const body = res.compressed;
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

