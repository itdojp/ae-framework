import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: estimateTokens monotonicity', () => {
  it(formatGWT('short text', 'append longer text', 'estimated tokens do not decrease'), () => {
    const opt = new TokenOptimizer();
    const a = 'abc';
    const b = a + ' defghijklmnop';
    expect(opt.estimateTokens(b)).toBeGreaterThanOrEqual(opt.estimateTokens(a));
  });
});

