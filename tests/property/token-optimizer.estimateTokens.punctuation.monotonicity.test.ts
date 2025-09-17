import { describe, it, expect } from 'vitest';
import { estimateTokens } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: estimateTokens punctuation monotonicity', () => {
  it(
    formatGWT('base text', 'append punctuation/whitespace variants', 'token estimate does not decrease'),
    () => {
      const base = 'This is a sample text';
      const variants = [
        base + '.',
        base + '...',
        base + ' . ',
        base + ' — end',
      ];
      const baseEst = estimateTokens(base);
      for (const v of variants) {
        expect(estimateTokens(v)).toBeGreaterThanOrEqual(baseEst);
      }
    }
  );
});

