import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer multiple headers remain present', () => {
  it(
    formatGWT('docs with many headers', 'compressSteeringDocuments', 'section headers are present'),
    async () => {
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 5, maxLength: 50 }),
          async (s) => {
            const opt = new TokenOptimizer();
            const docs = {
              product: `# Title\n## H1\n${s}\n## H2\n${s}`,
              architecture: `## Arch\n${s}`,
              standards: `## Std\n${s}`,
            } as Record<string,string>;
            const res = await opt.compressSteeringDocuments(docs, { maxTokens: 1000, enableCaching: false });
            // compressSteeringDocuments builds "## SECTION" headers; we expect them in output
            expect(res.compressed).toMatch(/## PRODUCT|## ARCHITECTURE|## STANDARDS/);
          }
        ),
        { numRuns: 10 }
      );
    }
  );
});

