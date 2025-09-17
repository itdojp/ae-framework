import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer whitespace many-lines reduction (large)', () => {
  it(
    formatGWT('whitespace-heavy docs with many newlines', 'compressSteeringDocuments', 'tokens not increased; headers first'),
    async () => {
      const nl = Array.from({ length: 500 }).map(() => '').join('\n');
      const docs: Record<string,string> = {
        product: ['# product', nl, ('alpha '.repeat(180))].join('\n'),
        architecture: ['# architecture', nl, ('beta '.repeat(160))].join('\n')
      };
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 16000, enableCaching: false });
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
      const body = res.compressed;
      const iProd = body.indexOf('## PRODUCT');
      const iArch = body.indexOf('## ARCHITECTURE');
      expect(iProd).toBeGreaterThanOrEqual(0);
      expect(iArch).toBeGreaterThan(iProd);
    }
  );
});

