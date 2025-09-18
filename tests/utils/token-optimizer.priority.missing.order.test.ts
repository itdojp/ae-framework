import { describe, test, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer.js';

describe('TokenOptimizer — preservePriority with missing/extra sections', () => {
  test('orders present sections by preservePriority even if some are missing', async () => {
    const optimizer = new TokenOptimizer();
    const docs = {
      medium: 'Medium priority text',
      extra: 'Extra section not listed',
      high: 'High priority first',
    } as Record<string, string>;

    const res = await optimizer.compressSteeringDocuments(docs, {
      maxTokens: 500,
      preservePriority: ['high', 'medium', 'low']
    });

    const idxHigh = res.compressed.indexOf('## HIGH');
    const idxMedium = res.compressed.indexOf('## MEDIUM');
    expect(idxHigh).toBeGreaterThan(-1);
    expect(idxMedium).toBeGreaterThan(-1);
    expect(idxHigh).toBeLessThan(idxMedium);
    // Extra section should appear after known priorities
    const idxExtra = res.compressed.indexOf('## EXTRA');
    expect(idxExtra).toBeGreaterThan(idxMedium);
  });
});

