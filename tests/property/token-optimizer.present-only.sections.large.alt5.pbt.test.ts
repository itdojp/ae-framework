import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer present-only sections (large alt5)', () => {
  it(
    formatGWT('present-only docs', 'compress large docs with missing sections', 'non-present sections are not introduced'),
    async () => {
      const docs: Record<string,string> = {
        product: '# product\n' + 'A'.repeat(3000),
        architecture: '# arch\n' + 'B'.repeat(2000),
        // standards は欠損
      } as any;
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, { maxTokens: 8000, compressionLevel: 'medium' });
      const body = res.compressed;
      expect(body.includes('## STANDARDS')).toBe(false);
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
    }
  );
});

