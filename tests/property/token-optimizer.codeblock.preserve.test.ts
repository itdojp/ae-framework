import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: code blocks are preserved', () => {
  it(formatGWT('text with ```code``` block', 'compressText indirectly via optimizeContext', 'code fences are preserved'), async () => {
    const opt = new TokenOptimizer();
    const code = ['```js', 'function add(a,b){ return a+b }', '```'].join('\n');
    const ctx = `para before\n\n${code}\n\npara after`;
    const { optimized } = await opt.optimizeContext(ctx, 500, ['add']);
    expect(optimized).toContain('```');
    expect(optimized).toContain('function add');
  });
});

