import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer preservePriority missing top two', () => {
  it(
    formatGWT('docs without top two priorities', 'compressSteeringDocuments', 'third priority section appears first'),
    async () => {
      const docs = {
        architecture: 'A arch',
        standards: 'S std',
        // product and design missing (top two example)
      } as Record<string, string>;
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, {
        preservePriority: ['product', 'design', 'architecture', 'standards'],
        maxTokens: 120,
        enableCaching: false,
      });
      if (res.compressed.trim().length > 0) {
        expect(res.compressed.trim().startsWith('## ARCHITECTURE')).toBe(true);
      }
    }
  );
});

