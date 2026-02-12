import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { describe, expect, it } from 'vitest';

import { DocumentationTester } from '../../../scripts/doctest.ts';

describe('DocumentationTester', () => {
  it('validates code blocks in ESM runtime without require errors', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'doctest-fixture-'));

    try {
      writeFileSync(join(fixtureDir, 'linked.md'), '# linked');
      writeFileSync(
        join(fixtureDir, 'sample.md'),
        [
          '# Sample',
          '',
          '```bash',
          'echo "ok"',
          '```',
          '',
          '```json',
          '{"hello":"world"}',
          '```',
          '',
          '```javascript',
          'const n = 1;',
          'console.log(n);',
          '```',
          '',
          '[linked](./linked.md)',
          '',
        ].join('\n')
      );

      const tester = new DocumentationTester();
      const result = await tester.runDocTests(join(fixtureDir, '*.md'));

      expect(result.codeBlocks.total).toBe(3);
      expect(result.codeBlocks.failed).toBe(0);
      expect(result.links.invalid).toBe(0);
      expect(
        result.codeBlocks.results.some((entry) => String(entry.error || '').includes('require is not defined'))
      ).toBe(false);
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
    }
  });
});
