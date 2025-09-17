import { describe, it, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer';
import { formatGWT } from '../utils/gwt-format';

describe('TokenOptimizer truncate sentinel (alt2)', () => {
  it(
    formatGWT('many large sections', 'compress with very small maxTokens', 'appends [...truncated] sentinel and no absent sections introduced'),
    async () => {
      const docs: Record<string,string> = {
        product: '# product\n' + 'alpha '.repeat(200),
        architecture: '# architecture\n' + 'beta '.repeat(200),
        standards: '# standards\n' + 'gamma '.repeat(200)
      };
      const opt = new TokenOptimizer();
      const { compressed, stats } = await opt.compressSteeringDocuments(docs, { maxTokens: 200, enableCaching: false });
      expect(stats.compressed).toBeLessThanOrEqual(200);
      expect(compressed.includes('[...truncated]')).toBe(true);
      expect(compressed.includes('## DESIGN')).toBe(false);
    }
  );
});

