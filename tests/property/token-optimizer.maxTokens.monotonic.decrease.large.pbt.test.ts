import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer maxTokens monotonic decrease (large)', () => {
  it(
    formatGWT('same docs', 'decrease maxTokens', 'compressed tokens do not increase'),
    async () => {
      const docs: Record<string,string> = {
        product: '# product\n' + 'alpha '.repeat(200),
        architecture: '# architecture\n' + 'beta '.repeat(180)
      };
      const opt = new TokenOptimizer();
      const r1 = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 16000, enableCaching: false });
      const r2 = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 12000, enableCaching: false });
      expect(r2.stats.compressed).toBeLessThanOrEqual(r1.stats.compressed);
    }
  );
});

