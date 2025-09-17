import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer: sections order stable by preservePriority', () => {
  it(
    formatGWT('subset of sections', 'compressSteeringDocuments', 'headers follow preservePriority order among included'),
    async () => {
      const docs = {
        standards: 'S',
        architecture: 'A',
        product: 'P',
      } as Record<string,string>;
      const opt = new TokenOptimizer();
      const res = await opt.compressSteeringDocuments(docs, {
        preservePriority: ['product','design','architecture','standards'],
        maxTokens: 200,
        enableCaching: false,
      });
      const body = res.compressed.trim();
      const iP = body.indexOf('## PRODUCT');
      const iA = body.indexOf('## ARCHITECTURE');
      const iS = body.indexOf('## STANDARDS');
      const idx = [iP, iA, iS].filter(i => i >= 0);
      if (idx.length >= 2) {
        expect(iP).toBeLessThan(iA === -1 ? 1e9 : iA);
        expect((iA === -1 ? 1e9 : iA)).toBeLessThan(iS === -1 ? 1e9 : iS);
      }
    }
  );
});

