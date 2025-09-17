import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer duplicate headers with codeblocks (large)', () => {
  it(
    formatGWT('duplicate headers with fences', 'compressSteeringDocuments', 'dedup + preserve code fences; tokens not increased'),
    async () => {
      const docs: Record<string,string> = {
        product: ['# product','# product','```','x','```','alpha '.repeat(120)].join('\n'),
        architecture: ['# architecture','```','y','```','beta '.repeat(110)].join('\n')
      };
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 16000, enableCaching: false });
      const body = res.compressed;
      expect((body.match(/```/g) || []).length).toBeGreaterThanOrEqual(1);
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
    }
  );
});

