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

function captureStdout(fn: () => void): string {
  const originalWrite = process.stdout.write;
  let output = '';
  process.stdout.write = ((chunk: unknown, encoding?: unknown, callback?: unknown) => {
    if (typeof chunk === 'string') {
      output += chunk;
    } else if (chunk) {
      output += Buffer.from(chunk as Uint8Array).toString(typeof encoding === 'string' ? encoding : undefined);
    }
    if (typeof callback === 'function') {
      callback();
    }
    return true;
  }) as typeof process.stdout.write;
  try {
    fn();
  } finally {
    process.stdout.write = originalWrite;
  }
  return output;
}

describe('check-root-layout', () => {
  it('detects forbidden root files', () => {
    const result = scanRootLayout([
      'src',
      'docs',
      'cegis-report-1234.json',
      'drift-report-src-generated.json',
      'verify-lite-run-summary.json',
      'verify-lite-lint.log',
      'verify-lite-lint-summary.json',
    ]);

    expect(result.violations.map((v) => v.entry)).toEqual([
      'cegis-report-1234.json',
      'drift-report-src-generated.json',
      'verify-lite-lint-summary.json',
      'verify-lite-lint.log',
      'verify-lite-run-summary.json',
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

  it('treats reports directories as allowed root entries', () => {
    const result = scanRootLayout([
      'reports',
      'temp-reports',
      'src',
    ]);

    expect(result.violations).toHaveLength(0);
    expect(result.warnings).toHaveLength(0);
  });

  it('supports per-entry override for local checks', () => {
    const result = scanRootLayout(
      [
        'node_modules',
        'src',
      ],
      { allowEntries: ['node_modules'] },
    );

    expect(result.violations).toHaveLength(0);
    expect(result.warnings).toHaveLength(0);
  });

  it('returns exit code 1 in strict mode when violation exists', () => {
    withTempDir((dir) => {
      writeFileSync(path.join(dir, 'cegis-report-100.json'), '{}');
      mkdirSync(path.join(dir, 'src'));
      captureStdout(() => {
        const outcome = runRootLayoutCheck(['node', 'check-root-layout.mjs', `--root=${dir}`, '--mode=strict']);
        expect(outcome.exitCode).toBe(1);
      });
    });
  });

  it('returns exit code 0 in warn mode even when violations exist', () => {
    withTempDir((dir) => {
      writeFileSync(path.join(dir, 'conformance-results.json'), '{}');
      mkdirSync(path.join(dir, 'src'));
      captureStdout(() => {
        const outcome = runRootLayoutCheck(['node', 'check-root-layout.mjs', `--root=${dir}`, '--mode=warn']);
        expect(outcome.exitCode).toBe(0);
        expect(outcome.violations).toHaveLength(1);
      });
    });
  });

  it('outputs valid JSON in strict mode when --format=json is used', () => {
    withTempDir((dir) => {
      writeFileSync(path.join(dir, 'cegis-report-100.json'), '{}');
      mkdirSync(path.join(dir, 'src'));
      const output = captureStdout(() => {
        const outcome = runRootLayoutCheck([
          'node',
          'check-root-layout.mjs',
          `--root=${dir}`,
          '--mode=strict',
          '--format=json',
        ]);
        expect(outcome.exitCode).toBe(1);
      });

      const parsed = JSON.parse(output);
      expect(parsed.mode).toBe('strict');
      expect(parsed.exitCode).toBe(1);
      expect(parsed.violations).toHaveLength(1);
      expect(parsed.warnings).toHaveLength(0);
    });
  });

  it('returns exit code 0 in strict mode when forbidden entry is explicitly allowed', () => {
    withTempDir((dir) => {
      mkdirSync(path.join(dir, 'node_modules'));
      mkdirSync(path.join(dir, 'src'));
      captureStdout(() => {
        const outcome = runRootLayoutCheck([
          'node',
          'check-root-layout.mjs',
          `--root=${dir}`,
          '--mode=strict',
          '--allow-entry=node_modules',
        ]);
        expect(outcome.exitCode).toBe(0);
        expect(outcome.violations).toHaveLength(0);
      });
    });
  });

  it('outputs valid JSON in warn mode when --format=json is used', () => {
    withTempDir((dir) => {
      writeFileSync(path.join(dir, 'conformance-results.json'), '{}');
      mkdirSync(path.join(dir, 'src'));
      const output = captureStdout(() => {
        const outcome = runRootLayoutCheck([
          'node',
          'check-root-layout.mjs',
          `--root=${dir}`,
          '--mode=warn',
          '--format=json',
        ]);
        expect(outcome.exitCode).toBe(0);
      });

      const parsed = JSON.parse(output);
      expect(parsed.mode).toBe('warn');
      expect(parsed.exitCode).toBe(0);
      expect(parsed.violations).toHaveLength(1);
      expect(parsed.warnings).toHaveLength(0);
    });
  });

  it('reports a read error when root directory does not exist', () => {
    withTempDir((dir) => {
      const missingDir = path.join(dir, 'missing');
      const output = captureStdout(() => {
        const outcome = runRootLayoutCheck([
          'node',
          'check-root-layout.mjs',
          `--root=${missingDir}`,
          '--mode=strict',
          '--format=json',
        ]);
        expect(outcome.exitCode).toBe(1);
        expect(outcome.violations[0]?.type).toBe('read_error');
      });

      const parsed = JSON.parse(output);
      expect(parsed.exitCode).toBe(1);
      expect(parsed.violations[0]?.type).toBe('read_error');
      expect(parsed.violations[0]?.entry).toBe(missingDir);
    });
  });

  it('treats URL-escaped module path and argv path as the same file', () => {
    const metaUrl = 'file:///tmp/with%20space/check-root-layout.mjs';
    const argvPath = '/tmp/with space/check-root-layout.mjs';
    expect(isExecutedAsMain(metaUrl, argvPath)).toBe(true);
  });
});
