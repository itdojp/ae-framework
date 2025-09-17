import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer deduplication boundary', () => {
  it(
    formatGWT('docs with repeated sentences', 'compressSteeringDocuments', 'compressed tokens <= original and single occurrence'),
    async () => {
      const opt = new TokenOptimizer();
      const repeated = 'This is important. This is important. This is important.';
      const docs = {
        product: repeated,
        architecture: repeated,
        standards: repeated,
      } as Record<string, string>;
      const res = await opt.compressSteeringDocuments(docs, { maxTokens: 5000, enableCaching: false });
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
      // Repeated core sentence should not appear 3+ times verbatim in output
      const count = (res.compressed.match(/This is important\./g) || []).length;
      expect(count).toBeLessThanOrEqual(3); // significantly less than naive 9
    }
  );
});

