import { existsSync, mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  cleanRootSafeRemove,
  collectSafeRemoveTargets,
  isExecutedAsMain,
} from '../../../scripts/project/clean-root-safe-remove.mjs';

function withTempDir(fn: (dir: string) => void): void {
  const dir = mkdtempSync(path.join(tmpdir(), 'ae-clean-root-'));
  try {
    fn(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

describe('clean-root-safe-remove', () => {
  it('collects file and directory targets by policy', () => {
    withTempDir((dir) => {
      writeFileSync(path.join(dir, 'generated-suite.json'), '{}');
      writeFileSync(path.join(dir, 'drift-report-src-generated.json'), '{}');
      writeFileSync(path.join(dir, 'run-test.json'), '{}');
      mkdirSync(path.join(dir, 'coverage'));
      mkdirSync(path.join(dir, 'src'));

      const targets = collectSafeRemoveTargets(dir);

      expect(targets.files).toContain('generated-suite.json');
      expect(targets.files).toContain('drift-report-src-generated.json');
      expect(targets.files).toContain('run-test.json');
      expect(targets.dirs).toContain('coverage');
      expect(targets.dirs).not.toContain('src');
    });
  });

  it('includes node_modules only when deep option is enabled', () => {
    withTempDir((dir) => {
      mkdirSync(path.join(dir, 'node_modules'));

      const defaultTargets = collectSafeRemoveTargets(dir);
      const deepTargets = collectSafeRemoveTargets(dir, { includeNodeModules: true });

      expect(defaultTargets.dirs).not.toContain('node_modules');
      expect(deepTargets.dirs).toContain('node_modules');
    });
  });

  it('does not remove files in dry-run mode', () => {
    withTempDir((dir) => {
      writeFileSync(path.join(dir, 'workflow-test.json'), '{}');
      mkdirSync(path.join(dir, 'tmp'));

      const outcome = cleanRootSafeRemove(dir, { dryRun: true });

      expect(outcome.failed).toHaveLength(0);
      expect(outcome.removed).toEqual(expect.arrayContaining([
        'workflow-test.json',
        'tmp',
      ]));
      expect(existsSync(path.join(dir, 'workflow-test.json'))).toBe(true);
      expect(existsSync(path.join(dir, 'tmp'))).toBe(true);
    });
  });

  it('removes safe-remove targets and keeps unrelated files', () => {
    withTempDir((dir) => {
      writeFileSync(path.join(dir, 'conformance-results.json'), '{}');
      writeFileSync(path.join(dir, 'keep.json'), '{}');
      mkdirSync(path.join(dir, 'test-results-run'));

      const outcome = cleanRootSafeRemove(dir, { dryRun: false });

      expect(outcome.failed).toHaveLength(0);
      expect(existsSync(path.join(dir, 'conformance-results.json'))).toBe(false);
      expect(existsSync(path.join(dir, 'test-results-run'))).toBe(false);
      expect(existsSync(path.join(dir, 'keep.json'))).toBe(true);
    });
  });

  it('treats URL-escaped module path and argv path as the same file', () => {
    const metaUrl = 'file:///tmp/with%20space/clean-root-safe-remove.mjs';
    const argvPath = '/tmp/with space/clean-root-safe-remove.mjs';
    expect(isExecutedAsMain(metaUrl, argvPath)).toBe(true);
  });
});
