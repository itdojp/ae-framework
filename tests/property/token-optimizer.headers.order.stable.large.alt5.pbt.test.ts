import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer headers order stable (large alt5)', () => {
  it(
    formatGWT('large docs', 'compress with standard priority', 'headers remain in PRODUCT > ARCHITECTURE > STANDARDS order'),
    async () => {
      const product = ['# product', 'A'.repeat(3000)].join('\n');
      const architecture = ['# architecture', 'B'.repeat(2000)].join('\n');
      const standards = ['# standards', 'C'.repeat(1000)].join('\n');
      const docs: Record<string,string> = { product, architecture, standards };
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','architecture','standards'], maxTokens: 9000 });
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

