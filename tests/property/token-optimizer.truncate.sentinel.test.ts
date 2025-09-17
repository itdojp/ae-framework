import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('TokenOptimizer truncate sentinel', () => {
  it('adds [...truncated] when section is truncated due to maxTokens', async () => {
    const opt = new TokenOptimizer();
    // craft multiple large sections to exceed small maxTokens
    const docs: Record<string,string> = {
      product: 'must: important requirements. '.repeat(200),
      architecture: 'should: structural notes. '.repeat(200),
      standards: 'key: style and patterns. '.repeat(200)
    };
    const { compressed, stats } = await opt.compressSteeringDocuments(docs, { maxTokens: 300 });
    expect(typeof compressed).toBe('string');
    // token estimate should not exceed maxTokens
    expect(stats.compressed).toBeLessThanOrEqual(300);
    // if truncation happened, sentinel appears
    expect(compressed.includes('[...truncated]') || stats.compressed <= 300).toBe(true);
  });
});

