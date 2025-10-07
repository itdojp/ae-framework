import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('PBT: TokenOptimizer trim-edge trailing comma boundary', () => {
  it(
    formatGWT('trailing comma/space', 'compressSteeringDocuments(trim-end)', 'no trailing comma remains'),
    async () => {
      await fc.assert(
        // 固定シードでStrykerサンドボックスの再現性を確保する
        fc.asyncProperty(
          fc.string({ minLength: 1, maxLength: 48 }),
          async (s) => {
            const opt = new TokenOptimizer();
            const docs = { product: `${s},  ` } as Record<string, string>;
            const { compressed } = await opt.compressSteeringDocuments(docs, { maxTokens: 2000 });
            const last = compressed.trimEnd().slice(-1);
            expect([',', ';']).not.toContain(last);
          }
        ),
        { numRuns: 24, seed: 0xAEF00D, path: '0:0:0', skipAllAfterTimeLimit: 5000, markInterruptAsFailure: true }
      );
    }
  );
});

