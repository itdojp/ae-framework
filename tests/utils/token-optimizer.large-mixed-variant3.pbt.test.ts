import { describe, test, expect } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer.js';

// Large mixed variant: headers + bullets + code fences + prose
describe('TokenOptimizer — large mixed variant 3 (PBT-lite)', () => {
  test('preserves code fences and reduces tokens non-negatively', async () => {
    const optimizer = new TokenOptimizer();
    const headers = Array.from({ length: 30 }, (_, i) => `# H${i}\nSub ${i}`).join('\n');
    const bullets = Array.from({ length: 60 }, (_, i) => `- item ${i}`).join('\n');
    const code = Array.from({ length: 10 }, (_, i) => `\n\n\`\`\`ts\nfunction v${i}(){ return ${i}; }\n\`\`\``).join('\n');
    const prose = 'Important: keep signals. '.repeat(600);
    const docs = { product: headers + '\n' + prose, standards: bullets, architecture: code } as Record<string, string>;
    const res = await optimizer.compressSteeringDocuments(docs, { maxTokens: 3500, compressionLevel: 'high' });
    // Code fences should survive
    expect((res.compressed.match(/```/g) || []).length).toBeGreaterThanOrEqual(1);
    // Reduction percentage is >= 0
    expect(res.stats.reductionPercentage).toBeGreaterThanOrEqual(0);
  });
});

