import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: only present sections appear', () => {
  it(
    formatGWT('docs without design', 'compressSteeringDocuments', 'no DESIGN header in output'),
    async () => {
      const docs = { product: 'P', architecture: 'A' } as Record<string,string>;
      const opt = new TokenOptimizer();
      const { compressed } = await opt.compressSteeringDocuments(docs, {
        preservePriority: ['product','design','architecture','standards'],
        maxTokens: 200,
        enableCaching: false,
      });
      expect(compressed.includes('## DESIGN')).toBe(false);
    }
  );
});

