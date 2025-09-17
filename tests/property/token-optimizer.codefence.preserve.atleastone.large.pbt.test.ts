import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer codefence preserve at least one (large)', () => {
  it(
    formatGWT('two fences in input', 'compressSteeringDocuments', 'at least one code fence remains; tokens not increased'),
    async () => {
      const docs: Record<string,string> = {
        product: ['# product','```ts','const a=1;','```','lorem '.repeat(100),'```','const b=2;','```'].join('\n'),
        architecture: ['# architecture','ipsum '.repeat(120)].join('\n')
      };
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 14000, enableCaching: false });
      const body = res.compressed;
      expect((body.match(/```/g) || []).length).toBeGreaterThanOrEqual(1);
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
    }
  );
});

