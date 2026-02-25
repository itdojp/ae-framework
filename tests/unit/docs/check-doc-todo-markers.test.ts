import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  collectTodoMarkerViolations,
  parseArgs,
  runDocTodoMarkerCheck,
} from '../../../scripts/docs/check-doc-todo-markers.mjs';

function withTempRepo(testFn: (rootDir: string) => void): void {
  const rootDir = mkdtempSync(path.join(tmpdir(), 'ae-doc-todo-'));
  try {
    testFn(rootDir);
  } finally {
    rmSync(rootDir, { recursive: true, force: true });
  }
}

describe('check-doc-todo-markers', () => {
  it('parses default args', () => {
    const result = parseArgs(['node', 'check-doc-todo-markers.mjs']);
    expect(result.docsProvided).toBe(false);
    expect(result.docs).toEqual([]);
  });

  it('detects heading TODO markers without issue refs', () => {
    const violations = collectTodoMarkerViolations('docs/ci/sample.md', [
      '## TODO',
      '- FIXME next',
      '```ts',
      '// TODO: this is code and ignored',
      '```',
    ].join('\n'));

    expect(violations).toHaveLength(2);
    expect(violations[0]).toEqual(expect.objectContaining({
      line: 1,
      markdownPath: 'docs/ci/sample.md',
    }));
  });

  it('accepts TODO/FIXME with issue references', () => {
    const violations = collectTodoMarkerViolations('docs/ci/sample.md', [
      '## TODO(#1234)',
      '- FIXME(#1234): follow-up',
    ].join('\n'));
    expect(violations).toHaveLength(0);
  });

  it('scans docs/ci by default and reports violations', () => {
    withTempRepo((rootDir) => {
      mkdirSync(path.join(rootDir, 'docs/ci'), { recursive: true });
      writeFileSync(path.join(rootDir, 'docs/ci/ok.md'), '## TODO(#1234)');
      writeFileSync(path.join(rootDir, 'docs/ci/ng.md'), '## TODO');

      const result = runDocTodoMarkerCheck([
        'node',
        'check-doc-todo-markers.mjs',
        `--root=${rootDir}`,
      ]);

      expect(result.docsScanned).toEqual(['docs/ci/ng.md', 'docs/ci/ok.md']);
      expect(result.exitCode).toBe(1);
      expect(result.violations).toHaveLength(1);
      expect(result.violations[0]).toEqual(expect.objectContaining({
        markdownPath: 'docs/ci/ng.md',
      }));
    });
  });
});
