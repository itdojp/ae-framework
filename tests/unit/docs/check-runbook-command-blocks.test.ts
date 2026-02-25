import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  extractShellBlocks,
  parseArgs,
  runRunbookCommandCheck,
  validateShellSyntax,
} from '../../../scripts/docs/check-runbook-command-blocks.mjs';

function withTempRepo(testFn: (rootDir: string) => void): void {
  const rootDir = mkdtempSync(path.join(tmpdir(), 'ae-runbook-check-'));
  try {
    testFn(rootDir);
  } finally {
    rmSync(rootDir, { recursive: true, force: true });
  }
}

describe('check-runbook-command-blocks', () => {
  it('parses default args', () => {
    const result = parseArgs(['node', 'check-runbook-command-blocks.mjs']);
    expect(result.docsProvided).toBe(false);
    expect(result.docs).toEqual(expect.arrayContaining([
      'docs/ci/ci-troubleshooting-guide.md',
      'docs/ci/pr-automation.md',
    ]));
  });

  it('extracts shell blocks only for shell fences', () => {
    const blocks = extractShellBlocks([
      '```yaml',
      'name: example',
      '```',
      '```bash',
      'echo ok',
      '```',
      '```sh',
      'echo also-ok',
      '```',
    ].join('\n'));

    expect(blocks).toHaveLength(2);
    expect(blocks[0].content).toContain('echo ok');
    expect(blocks[1].content).toContain('echo also-ok');
  });

  it('validates shell syntax with placeholder sanitization', () => {
    const valid = validateShellSyntax('gh workflow run test -f pr_number=<PR番号>');
    expect(valid.ok).toBe(true);

    const invalid = validateShellSyntax('if then echo broken fi');
    expect(invalid.ok).toBe(false);
  });

  it('reports syntax error for malformed shell fence', () => {
    withTempRepo((rootDir) => {
      mkdirSync(path.join(rootDir, 'docs/ci'), { recursive: true });
      writeFileSync(path.join(rootDir, 'docs/ci/sample.md'), [
        '```bash',
        'if then echo broken fi',
        '```',
      ].join('\n'));

      const result = runRunbookCommandCheck([
        'node',
        'check-runbook-command-blocks.mjs',
        `--root=${rootDir}`,
        '--docs=docs/ci/sample.md',
      ]);

      expect(result.exitCode).toBe(1);
      expect(result.syntaxErrors).toHaveLength(1);
      expect(result.shellBlocksScanned).toBe(1);
    });
  });

  it('passes when runbook shell blocks are valid', () => {
    withTempRepo((rootDir) => {
      mkdirSync(path.join(rootDir, 'docs/ci'), { recursive: true });
      writeFileSync(path.join(rootDir, 'docs/ci/sample.md'), [
        '```bash',
        'set -euo pipefail',
        'gh run rerun 123 --failed',
        '```',
      ].join('\n'));

      const result = runRunbookCommandCheck([
        'node',
        'check-runbook-command-blocks.mjs',
        `--root=${rootDir}`,
        '--docs=docs/ci/sample.md',
      ]);

      expect(result.exitCode).toBe(0);
      expect(result.syntaxErrors).toHaveLength(0);
      expect(result.docsScanned).toEqual(['docs/ci/sample.md']);
    });
  });
});
