import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: empty docs', () => {
  it(formatGWT('docs = {}', 'compressSteeringDocuments', 'compressed empty and zero tokens'), async () => {
    const opt = new TokenOptimizer();
    const { compressed, stats } = await opt.compressSteeringDocuments({});
    expect(compressed).toBe('');
    expect(stats.original).toBe(0);
    expect(stats.compressed).toBe(0);
    expect(stats.reductionPercentage).toBe(0);
  });
});

