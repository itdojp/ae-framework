import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: preservePriority with tight maxTokens (edge)', () => {
  it(
    formatGWT('custom priority puts standards first', 'compress with very small maxTokens', 'first included section respects priority'),
    async () => {
      const opt = new TokenOptimizer();
      const docs = {
        product: 'must: product direction. '.repeat(5),
        architecture: 'should: arch notes. '.repeat(5),
        standards: 'key: style guide. '.repeat(5),
      } as Record<string, string>;
      const res = await opt.compressSteeringDocuments(docs, {
        preservePriority: ['standards', 'product', 'architecture'],
        maxTokens: 80,
        enableCaching: false,
      });
      // Whatever made it in first, it must start with STANDARDS header when any content exists
      if (res.compressed.trim().length > 0) {
        expect(res.compressed.trim().startsWith('## STANDARDS')).toBe(true);
      }
    }
  );
});

