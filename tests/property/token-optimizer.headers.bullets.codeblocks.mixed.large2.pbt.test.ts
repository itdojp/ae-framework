import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer headers+bullets+codeblocks mixed (large 2)', () => {
  it(
    formatGWT('mixed content', 'compressSteeringDocuments', 'headers first; at least one code fence kept; tokens reduced'),
    async () => {
      const docs: Record<string,string> = {
        product: [
          '# product',
          '- a',
          '```
block1
```
',
          '- a',
          ('lorem '.repeat(180))
        ].join('\n'),
        architecture: [
          '# architecture',
          '```
block2
```
',
          '- b',
          ('ipsum '.repeat(160))
        ].join('\n')
      };
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 14000, enableCaching: false });
      const body = res.compressed;
      expect((body.match(/```/g) || []).length).toBeGreaterThanOrEqual(1);
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
    }
  );
});

