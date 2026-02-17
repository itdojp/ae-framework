import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { isExecutedAsMain, runRootLayoutCheck, scanRootLayout } from '../../../scripts/ci/check-root-layout.mjs';

function withTempDir(fn: (dir: string) => void): void {
  const dir = mkdtempSync(path.join(tmpdir(), 'ae-root-layout-'));
  try {
    fn(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

describe('check-root-layout', () => {
  it('detects forbidden root files', () => {
    const result = scanRootLayout([
      'src',
      'docs',
      'cegis-report-1234.json',
      'verify-lite-lint-summary.json',
    ]);

    expect(result.violations.map((v) => v.entry)).toEqual([
      'cegis-report-1234.json',
      'verify-lite-lint-summary.json',
    ]);
    expect(result.warnings).toHaveLength(0);
  });

  it('reports unclassified non-dot entries as warnings', () => {
    const result = scanRootLayout([
      'src',
      'docs',
      'mystery',
      '.vscode',
    ]);

    expect(result.violations).toHaveLength(0);
    expect(result.warnings).toEqual([
      expect.objectContaining({ entry: 'mystery', type: 'unclassified_entry' }),
    ]);
  });

  it('returns exit code 1 in strict mode when violation exists', () => {
    withTempDir((dir) => {
      writeFileSync(path.join(dir, 'cegis-report-100.json'), '{}');
      mkdirSync(path.join(dir, 'src'));
      const originalWrite = process.stdout.write;
      process.stdout.write = (() => true) as typeof process.stdout.write;
      try {
        const outcome = runRootLayoutCheck(['node', 'check-root-layout.mjs', `--root=${dir}`, '--mode=strict']);
        expect(outcome.exitCode).toBe(1);
      } finally {
        process.stdout.write = originalWrite;
      }
    });
  });

  it('returns exit code 0 in warn mode even when violations exist', () => {
    withTempDir((dir) => {
      writeFileSync(path.join(dir, 'conformance-results.json'), '{}');
      mkdirSync(path.join(dir, 'src'));
      const originalWrite = process.stdout.write;
      process.stdout.write = (() => true) as typeof process.stdout.write;
      try {
        const outcome = runRootLayoutCheck(['node', 'check-root-layout.mjs', `--root=${dir}`, '--mode=warn']);
        expect(outcome.exitCode).toBe(0);
        expect(outcome.violations).toHaveLength(1);
      } finally {
        process.stdout.write = originalWrite;
      }
    });
  });

  it('treats URL-escaped module path and argv path as the same file', () => {
    const metaUrl = 'file:///tmp/with%20space/check-root-layout.mjs';
    const argvPath = '/tmp/with space/check-root-layout.mjs';
    expect(isExecutedAsMain(metaUrl, argvPath)).toBe(true);
  });
});
