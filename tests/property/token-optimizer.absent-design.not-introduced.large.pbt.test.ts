import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer absent design not introduced (large)', () => {
  it(
    formatGWT('docs without design', 'compressSteeringDocuments', 'no DESIGN section introduced'),
    async () => {
      const docs: Record<string,string> = {
        product: '# product\n' + 'alpha '.repeat(150),
        architecture: '# architecture\n' + 'beta '.repeat(120),
        standards: '# standards\n' + 'gamma '.repeat(100)
      };
      const opt = new TokenOptimizer();
      const { compressed, stats } = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 16000, enableCaching: false });
      expect(stats.compressed).toBeLessThanOrEqual(stats.original);
      expect(compressed.includes('## DESIGN')).toBe(false);
    }
  );
});

