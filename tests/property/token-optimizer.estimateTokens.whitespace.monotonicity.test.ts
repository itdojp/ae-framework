import { describe, it, expect } from 'vitest';
import { estimateTokens } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: estimateTokens whitespace monotonicity', () => {
  it(
    formatGWT('base text', 'append newlines/spaces', 'token estimate does not decrease'),
    () => {
      const base = 'A short sample';
      const variants = [
        base + '\n',
        base + '  ',
        base + '\n\n  ',
        base + '\n  more',
      ];
      const baseEst = estimateTokens(base);
      for (const v of variants) {
        expect(estimateTokens(v)).toBeGreaterThanOrEqual(baseEst);
      }
    }
  );
});

