import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer estimateTokens monotonic under trimming', () => {
  it(
    formatGWT('text with leading/trailing/multiple spaces', 'trim whitespaces', 'estimated tokens do not increase'),
    () => {
      const opt = new TokenOptimizer();
      fc.assert(
        fc.property(
          fc.string({ minLength: 1, maxLength: 200 }),
          (raw) => {
            const noisy = `  ${raw}  `.replace(/(.)/g, '$1 '); // insert spaces
            const trimmed = noisy.trim().replace(/\s+/g, ' ');
            expect(opt.estimateTokens(trimmed)).toBeLessThanOrEqual(opt.estimateTokens(noisy));
          }
        ),
        { numRuns: 50 }
      );
    }
  );
});

