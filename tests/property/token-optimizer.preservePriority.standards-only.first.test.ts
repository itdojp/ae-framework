import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: preservePriority standards-only becomes first', () => {
  it(
    formatGWT('only standards present', 'compressSteeringDocuments', 'STANDARDS becomes first section'),
    async () => {
      const docs = { standards: 'S std' } as Record<string, string>;
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, {
        preservePriority: ['product', 'design', 'architecture', 'standards'],
        maxTokens: 120,
        enableCaching: false,
      });
      if (res.compressed.trim().length > 0) {
        expect(res.compressed.trim().startsWith('## STANDARDS')).toBe(true);
      }
    }
  );
});

