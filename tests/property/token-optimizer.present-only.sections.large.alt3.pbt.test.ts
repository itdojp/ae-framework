import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer present-only sections (large alt3)', () => {
  it(
    formatGWT('docs with product only', 'compressSteeringDocuments', 'no absent sections introduced'),
    async () => {
      const docs: Record<string,string> = {
        product: '# product\n' + 'alpha '.repeat(180)
      };
      const opt = new TokenOptimizer();
      const { compressed, stats } = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 12000, enableCaching: false });
      expect(stats.compressed).toBeLessThanOrEqual(stats.original);
      expect(compressed.includes('## DESIGN')).toBe(false);
      expect(compressed.includes('## ARCHITECTURE')).toBe(false);
      expect(compressed.includes('## STANDARDS')).toBe(false);
    }
  );
});

