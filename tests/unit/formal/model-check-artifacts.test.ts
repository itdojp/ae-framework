import { describe, expect, it } from 'vitest';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import {
  assertSafeModelCheckArtifactTarget,
  resolveModelCheckLogReference,
  validateModelCheckReferencedLogs,
} from '../../../scripts/verify/model-check-artifacts.mjs';

const tmpRoot = resolve('.codex-local/tmp');

function report(logPath: string) {
  return {
    tlc: {
      results: [{ log: logPath, evidence: { result: { logPath } } }],
    },
    alloy: { results: [] },
  };
}

describe('model-check artifact log resolution', () => {
  it('resolves every repository-relative log after artifact download', () => {
    mkdirSync(tmpRoot, { recursive: true });
    const root = mkdtempSync(join(tmpRoot, 'model-check-download-'));
    try {
      writeFileSync(join(root, 'Safe.tlc.log.txt'), 'TLC output\n', 'utf8');
      expect(resolveModelCheckLogReference('artifacts/codex/Safe.tlc.log.txt', root))
        .toBe(join(root, 'Safe.tlc.log.txt'));
      expect(validateModelCheckReferencedLogs(report('artifacts/codex/Safe.tlc.log.txt'), {
        artifactRoot: root,
      })).toEqual([]);
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });

  it.each([
    ['missing', (root: string) => undefined],
    ['directory', (root: string) => mkdirSync(join(root, 'Safe.tlc.log.txt'))],
  ])('rejects a %s referenced log', (_name, arrange) => {
    mkdirSync(tmpRoot, { recursive: true });
    const root = mkdtempSync(join(tmpRoot, 'model-check-invalid-log-'));
    try {
      arrange(root);
      expect(validateModelCheckReferencedLogs(report('artifacts/codex/Safe.tlc.log.txt'), {
        artifactRoot: root,
      }).join('\n')).toContain('referenced log is invalid');
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });

  it('rejects symlinked referenced logs and pre-existing symlink write targets', () => {
    if (process.platform === 'win32') return;
    mkdirSync(tmpRoot, { recursive: true });
    const root = mkdtempSync(join(tmpRoot, 'model-check-symlink-log-'));
    try {
      const outside = join(root, 'outside.txt');
      writeFileSync(outside, 'outside\n', 'utf8');
      const target = join(root, 'Safe.tlc.log.txt');
      symlinkSync(outside, target);
      expect(() => resolveModelCheckLogReference('artifacts/codex/Safe.tlc.log.txt', root))
        .toThrow('regular non-symlink file');
      expect(() => assertSafeModelCheckArtifactTarget(target, root)).toThrow('regular non-symlink file');
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });

  it('rejects absolute, traversing, or non-artifact-root log references', () => {
    mkdirSync(tmpRoot, { recursive: true });
    const root = mkdtempSync(join(tmpRoot, 'model-check-path-log-'));
    try {
      for (const logPath of ['/private/log.txt', '../log.txt', 'artifacts/other/log.txt']) {
        expect(validateModelCheckReferencedLogs(report(logPath), { artifactRoot: root }).length).toBeGreaterThan(0);
      }
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });
});
