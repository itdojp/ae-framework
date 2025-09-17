import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: processDocument strips comments (via compressSteeringDocuments)', () => {
  it(formatGWT('content with // and /* */ comments', 'compressSteeringDocuments', 'no comment markers remain'), async () => {
    const opt = new TokenOptimizer();
    const content = `function x(){\n// inline comment\n/* block comment */\nreturn 1;\n}`;
    const docs = { product: content };
    const { compressed } = await opt.compressSteeringDocuments(docs, { compressionLevel: 'medium', maxTokens: 2000 });
    expect(compressed.includes('//')).toBe(false);
    expect(compressed.includes('/*')).toBe(false);
    expect(compressed.includes('*/')).toBe(false);
  });
});

