import { describe, test, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer.js';

describe('TokenOptimizer — code fences preserved (>=1)', () => {
  test('if input has >=1 code fence then output has >=1', async () => {
    const optimizer = new TokenOptimizer();
    const docs = {
      code: '```ts\nconst x=1;\n```\n' + 'Some prose. '.repeat(50)
    } as Record<string, string>;
    const res = await optimizer.compressSteeringDocuments(docs, { compressionLevel: 'high', maxTokens: 1200 });
    expect((res.compressed.match(/```/g) || []).length).toBeGreaterThanOrEqual(1);
  });
});

