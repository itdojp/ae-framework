import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: deduplication of repeated sentences', () => {
  it(formatGWT('repeated sentences', 'compressSteeringDocuments', 'deduplicate and keep sentence boundary'), async () => {
    const opt = new TokenOptimizer();
    const repeated = 'Alpha beta. Gamma delta. Gamma delta. Alpha beta.';
    const docs = { product: repeated };
    const { compressed } = await opt.compressSteeringDocuments(docs, { compressionLevel: 'medium', maxTokens: 2000 });
    // expect duplicates removed
    expect(compressed.toLowerCase().split('gamma delta').length - 1).toBeLessThanOrEqual(1);
    expect(compressed.toLowerCase().split('alpha beta').length - 1).toBeLessThanOrEqual(1);
    // ends with punctuation
    expect(/[.!?]$/.test(compressed.trim())).toBe(true);
  });
});

