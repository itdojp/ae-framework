import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: preservePriority section order', () => {
  it(formatGWT('docs include product/architecture/standards', 'compressSteeringDocuments', 'sections appear in preservePriority order'), async () => {
    const opt = new TokenOptimizer();
    const docs = {
      standards: 'key: style.',
      architecture: 'should: structure.',
      product: 'must: goals.'
    } as Record<string,string>;
    const { compressed } = await opt.compressSteeringDocuments(docs, { maxTokens: 2000 });
    const idxProd = compressed.indexOf('## PRODUCT');
    const idxArch = compressed.indexOf('## ARCHITECTURE');
    const idxStd = compressed.indexOf('## STANDARDS');
    expect(idxProd).toBeGreaterThanOrEqual(0);
    expect(idxArch).toBeGreaterThan(idxProd);
    expect(idxStd).toBeGreaterThan(idxArch);
  });
});

