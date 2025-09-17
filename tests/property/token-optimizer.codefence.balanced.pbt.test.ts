import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer code fences remain balanced', () => {
  it(
    formatGWT('docs with a code fence', 'compressSteeringDocuments', 'number of ``` is even (balanced)'),
    async () => {
      await fc.assert(
        fc.asyncProperty(fc.string({ minLength: 1, maxLength: 80 }), async (s) => {
          const code = '```ts\nconst v = 1;\n```';
          const content = ['# Title', s, code, s].join('\n');
          const opt = new TokenOptimizer();
          const { compressed } = await opt.compressSteeringDocuments({ product: content }, { maxTokens: 4000 });
          const fenceCount = (compressed.match(/```/g) || []).length;
          expect(fenceCount % 2).toBe(0);
        }),
        { numRuns: 8 }
      );
    }
  );
});

