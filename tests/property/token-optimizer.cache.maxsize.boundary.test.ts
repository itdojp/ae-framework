import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: cache maxSize boundary', () => {
  it(
    formatGWT('many distinct docs', 'compress with caching enabled', 'cache size does not exceed maxSize (eviction works)'),
    async () => {
      const opt = new TokenOptimizer();
      const maxDocs = 120;
      for (let i = 0; i < maxDocs; i++) {
        const docs = {
          product: `must: goal ${i}`,
          architecture: `should: ${i} ${'x'.repeat(i % 50)}`,
          standards: `key: rule ${i}`,
        } as Record<string, string>;
        await opt.compressSteeringDocuments(docs, { enableCaching: true, maxTokens: 1000 });
      }
      const stats = opt.getCacheStats();
      expect(stats.size).toBeLessThanOrEqual(stats.maxSize);
    }
  );
});

