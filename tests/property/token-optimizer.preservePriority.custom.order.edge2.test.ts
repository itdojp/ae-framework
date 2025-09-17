import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: preservePriority custom order (edge 2)', () => {
  it(
    formatGWT('priority [architecture, standards, product]', 'compress with tight maxTokens', 'first included section follows priority'),
    async () => {
      const opt = new TokenOptimizer();
      const docs = {
        product: 'must: '.repeat(40),
        architecture: 'should: '.repeat(40),
        standards: 'key: '.repeat(40),
      } as Record<string, string>;
      const res = await opt.compressSteeringDocuments(docs, {
        preservePriority: ['architecture', 'standards', 'product'],
        maxTokens: 60,
        enableCaching: false,
      });
      if (res.compressed.trim().length > 0) {
        expect(res.compressed.trim().startsWith('## ARCHITECTURE')).toBe(true);
      }
    }
  );
});

