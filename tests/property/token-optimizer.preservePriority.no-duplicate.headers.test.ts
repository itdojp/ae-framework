import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: no duplicate headers in output', () => {
  it(
    formatGWT('subset with repeats in input docs', 'compressSteeringDocuments', 'each included section header appears once'),
    async () => {
      const docs = {
        product: 'P one',
        architecture: 'A first',
        standards: 'S alpha\nS beta'
      } as Record<string,string>;
      const opt = new TokenOptimizer();
      const { compressed } = await opt.compressSteeringDocuments(docs, {
        preservePriority: ['product','design','architecture','standards'],
        maxTokens: 400,
        enableCaching: false,
      });
      const occurs = (header: string) => (compressed.match(new RegExp(header,'g')) || []).length;
      if (compressed.trim().length > 0) {
        expect(occurs('## PRODUCT')).toBeLessThanOrEqual(1);
        if (compressed.includes('## ARCHITECTURE')) expect(occurs('## ARCHITECTURE')).toBe(1);
        if (compressed.includes('## STANDARDS')) expect(occurs('## STANDARDS')).toBe(1);
      }
    }
  );
});

