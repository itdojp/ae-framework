import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: optimizeContext selects keyword-relevant chunks', () => {
  it(formatGWT('two paragraphs, one with keyword', 'optimizeContext with small maxTokens', 'include keyword paragraph'), async () => {
    const opt = new TokenOptimizer();
    const para1 = 'This is general information without special terms. '.repeat(10);
    const para2 = 'Security policy and authentication must be enforced. '.repeat(6);
    const context = `${para1}\n\n${para2}`;
    const { optimized, stats } = await opt.optimizeContext(context, 200, ['security', 'authentication']);
    expect(typeof optimized).toBe('string');
    expect(stats.compressed).toBeLessThanOrEqual(200);
    expect(optimized.toLowerCase()).toContain('security');
  });
});

