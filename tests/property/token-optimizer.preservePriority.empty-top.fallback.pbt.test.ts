import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer preservePriority empty top falls back', () => {
  it(
    formatGWT('product empty, design present', 'compressSteeringDocuments', 'DESIGN becomes first section'),
    async () => {
      const docs = {
        product: '',
        design: 'D design',
        architecture: 'A arch'
      } as Record<string, string>;
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, {
        preservePriority: ['product', 'design', 'architecture', 'standards'],
        maxTokens: 200,
        enableCaching: false,
      });
      if (res.compressed.trim().length > 0) {
        expect(res.compressed.trim().startsWith('## DESIGN')).toBe(true);
      }
    }
  );
});

