import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  isExecutedAsMain,
  runRootGeneratedFilesCheck,
  scanRootGeneratedFiles,
} from '../../../scripts/ci/check-no-root-generated-files.mjs';

function withTempDir(fn: (dir: string) => void): void {
  const dir = mkdtempSync(path.join(tmpdir(), 'ae-root-generated-'));
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

describe('check-no-root-generated-files', () => {
  it('detects forbidden generated files in repository root', () => {
    const violations = scanRootGeneratedFiles([
      'src',
      'docs',
      'verify-lite-run-summary.json',
      'verify-lite-lint-summary.json',
      'verify-lite-lint.log',
    ]);
    expect(violations.map((v) => v.entry)).toEqual([
      'verify-lite-lint-summary.json',
      'verify-lite-lint.log',
      'verify-lite-run-summary.json',
    ]);
  });

  it('ignores regular directories such as node_modules and coverage', () => {
    const violations = scanRootGeneratedFiles([
      'node_modules',
      'coverage',
      'src',
      'docs',
    ]);
    expect(violations).toHaveLength(0);
  });

  it('returns exit code 1 when forbidden files exist', () => {
    withTempDir((dir) => {
      writeFileSync(path.join(dir, 'verify-lite-run-summary.json'), '{}');
      mkdirSync(path.join(dir, 'src'));
      const output = captureStdout(() => {
        const result = runRootGeneratedFilesCheck([
          'node',
          'check-no-root-generated-files.mjs',
          `--root=${dir}`,
          '--format=json',
        ]);
        expect(result.exitCode).toBe(1);
      });
      const parsed = JSON.parse(output);
      expect(parsed.exitCode).toBe(1);
      expect(parsed.violations).toHaveLength(1);
      expect(parsed.violations[0]?.entry).toBe('verify-lite-run-summary.json');
    });
  });

  it('returns exit code 0 when forbidden files do not exist', () => {
    withTempDir((dir) => {
      mkdirSync(path.join(dir, 'src'));
      mkdirSync(path.join(dir, 'node_modules'));
      const output = captureStdout(() => {
        const result = runRootGeneratedFilesCheck([
          'node',
          'check-no-root-generated-files.mjs',
          `--root=${dir}`,
          '--format=json',
        ]);
        expect(result.exitCode).toBe(0);
      });
      const parsed = JSON.parse(output);
      expect(parsed.exitCode).toBe(0);
      expect(parsed.violations).toHaveLength(0);
    });
  });

  it('treats URL-escaped module path and argv path as the same file', () => {
    const metaUrl = 'file:///tmp/with%20space/check-no-root-generated-files.mjs';
    const argvPath = '/tmp/with space/check-no-root-generated-files.mjs';
    expect(isExecutedAsMain(metaUrl, argvPath)).toBe(true);
  });
});
