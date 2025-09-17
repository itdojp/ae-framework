import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: truncate end when no periods', () => {
  it(formatGWT('long text without periods', 'compress with very small maxTokens', 'tokens <= limit and reasonable tail'), async () => {
    const opt = new TokenOptimizer();
    const base = 'word '.repeat(1000);
    const docs = { product: base } as Record<string,string>;
    const { compressed, stats } = await opt.compressSteeringDocuments(docs, { maxTokens: 150 });
    expect(stats.compressed).toBeLessThanOrEqual(150);
    const tail = compressed.trim().slice(-20);
    expect(tail.includes('[...truncated]') || /\w$/.test(compressed.trim())).toBe(true);
  });
});

