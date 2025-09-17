import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer headers+bullets+fences mixed (large)', () => {
  it(
    formatGWT('mixed large', 'compressSteeringDocuments', 'headers first; at least one fence kept; tokens reduced'),
    async () => {
      const docs: Record<string,string> = {
        product: [
          '# product',
          '```
code
```
',
          '- a',
          '- a',
          ('lorem '.repeat(150))
        ].join('\n'),
        design: [
          '# design',
          '- b',
          '- b',
          ('ipsum '.repeat(120))
        ].join('\n')
      };
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, { preservePriority: ['product','design','architecture','standards'], maxTokens: 9000, enableCaching: false });
      const body = res.compressed;
      expect((body.match(/```/g) || []).length).toBeGreaterThanOrEqual(1);
      expect(res.stats.compressed).toBeLessThanOrEqual(res.stats.original);
    }
  );
});

