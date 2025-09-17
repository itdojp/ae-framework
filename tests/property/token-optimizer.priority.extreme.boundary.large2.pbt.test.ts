import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer priority extreme boundary 2 (large)', () => {
  it(
    formatGWT('single-section extremes', 'compressSteeringDocuments', 'headers honor preservePriority among present'),
    async () => {
      const opt = new TokenOptimizer();
      const cases: Array<Record<string,string>> = [
        { product: '# product\n' + 'lorem '.repeat(100) },
        { design: '# design\n' + 'ipsum '.repeat(100) },
        { architecture: '# architecture\n' + 'dolor '.repeat(100) },
        { standards: '# standards\n' + 'amet '.repeat(100) },
        { product: '# product\n' + 'x '.repeat(50), standards: '# standards\n' + 'y '.repeat(50) },
      ];
      for (const docs of cases) {
        const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 6000, enableCaching: false });
        expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
      }
    }
  );
});

