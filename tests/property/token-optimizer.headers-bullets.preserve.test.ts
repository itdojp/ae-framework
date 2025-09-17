import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: headers and bullets preserved', () => {
  it(formatGWT('text with headers/bullets', 'compressSteeringDocuments', 'keep headers and bullet lines present'), async () => {
    const opt = new TokenOptimizer();
    const content = ['# Title', '- item A', '- item B', 'paragraph'].join('\n');
    const docs = { product: content };
    const { compressed } = await opt.compressSteeringDocuments(docs, { compressionLevel: 'high', maxTokens: 2000 });
    expect(compressed.includes('# Title')).toBe(true);
    expect(compressed.includes('- item A')).toBe(true);
    expect(compressed.includes('- item B')).toBe(true);
  });
});

