import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('Smoke: TokenOptimizer huge input', () => {
  it('handles very large inputs and reduces or equals tokens', async () => {
    const huge = 'A'.repeat(20000) + '\n' + ('# Header\n' + 'code\n```js\nconsole.log(1)\n```\n').repeat(50);
    const docs = { product: huge, architecture: huge, standards: huge } as any;
    const opt = new TokenOptimizer();
    const { compressed, stats } = await opt.compressSteeringDocuments(docs, { maxTokens: 4000, compressionLevel: 'medium' });
    expect(typeof compressed).toBe('string');
    expect(stats.compressed).toBeLessThanOrEqual(stats.original);
  });
});

