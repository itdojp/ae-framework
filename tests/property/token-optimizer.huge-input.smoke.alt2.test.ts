import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';

describe('Smoke: TokenOptimizer huge input (alt2)', () => {
  it('handles headers+bullets+code fences heavy mix without increasing tokens', async () => {
    const headerBlock = Array.from({ length: 200 }, (_, i) => `# H${i}\n- a\n- b\n- c\n`).join('\n');
    const codeBlock = Array.from({ length: 100 }, () => '```ts\nconst x = 1;\n```').join('\n');
    const huge = headerBlock + '\n' + codeBlock + '\n' + 'Text '.repeat(5000);
    const docs = { product: huge, architecture: huge, standards: huge } as any;
    const opt = new TokenOptimizer();
    const { compressed, stats } = await opt.compressSteeringDocuments(docs, { maxTokens: 4000, compressionLevel: 'high' });
    expect(typeof compressed).toBe('string');
    expect(stats.compressed).toBeLessThanOrEqual(stats.original);
  });
});

