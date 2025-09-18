import { describe, test, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer.js';

describe('TokenOptimizer — huge input smoke (code fences preserved)', () => {
  test('preserves code fences and reduces tokens monotonically', async () => {
    const optimizer = new TokenOptimizer();
    const bigCode = Array.from({ length: 20 }, (_, i) => (
      '```ts\n' +
      `function f${i}(){ return ${i}; }\n` +
      '```\n'
    )).join('\n');
    const prose = 'Important: keep key points. '.repeat(200);
    const docs = { code: bigCode + prose };
    const low = await optimizer.compressSteeringDocuments(docs, { compressionLevel: 'low', maxTokens: 4000 });
    const high = await optimizer.compressSteeringDocuments(docs, { compressionLevel: 'high', maxTokens: 4000 });

    expect(low.compressed).toContain('```');
    expect(high.compressed).toContain('```');
    // High compression should not exceed low compression token count (allow tiny tolerance)
    expect(high.stats.compressed).toBeLessThanOrEqual(low.stats.compressed + 10);
  });
});

