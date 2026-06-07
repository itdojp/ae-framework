import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';

describe('LLM provider dynamic loading security', () => {
  it('TGT-012-F002: loads optional provider packages without eval-based dynamic code evaluation', () => {
    const files = [
      'src/providers/index.ts',
      'src/providers/llm-openai.ts',
      'src/providers/llm-anthropic.ts',
      'src/providers/llm-gemini.ts',
    ];

    for (const file of files) {
      const source = readFileSync(file, 'utf8');
      expect(source, file).not.toMatch(/\beval\s*\(/);
      expect(source, file).not.toMatch(/\bnew\s+Function\b/);
    }
  });
});
