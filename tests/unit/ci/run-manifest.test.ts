import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';

const generateScript = resolve('scripts/ci/generate-run-manifest.mjs');
const checkScript = resolve('scripts/ci/check-run-manifest.mjs');

function writeJson(p: string, data: unknown) {
  mkdirSync(dirname(p), { recursive: true });
  writeFileSync(p, JSON.stringify(data, null, 2), 'utf8');
}

function runNode(cwd: string, script: string, args: string[], env: Record<string, string>) {
  return spawnSync('node', [script, ...args], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env, ...env },
  });
}

describe('run-manifest (generate + check)', () => {
  it('detects fresh artifacts for the current commit', () => {
    const dir = mkdtempSync(join(tmpdir(), 'run-manifest-'));
    try {
      const commit = '0123456789abcdef0123456789abcdef01234567';

      const verifyLitePath = join(dir, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json');
      const envelopePath = join(dir, 'artifacts', 'report-envelope.json');

      writeJson(verifyLitePath, { metadata: { gitCommit: commit } });
      writeJson(envelopePath, { correlation: { commit } });

      const gen = runNode(
        dir,
        generateScript,
        ['--out', 'artifacts/run-manifest.json', '--top-level-command', 'unit-test'],
        { GIT_COMMIT: commit },
      );
      expect(gen.status).toBe(0);

      const manifestPath = join(dir, 'artifacts', 'run-manifest.json');
      const manifest = JSON.parse(readFileSync(manifestPath, 'utf8'));
      expect(manifest.metadata.gitCommit).toBe(commit);
      expect(manifest.summaries.verifyLite.status).toBe('present');
      expect(manifest.summaries.verifyLite.staleComparedToCurrentCommit).toBe(false);
      expect(manifest.summaries.reportEnvelope.status).toBe('present');
      expect(manifest.summaries.reportEnvelope.staleComparedToCurrentCommit).toBe(false);

      const check = runNode(
        dir,
        checkScript,
        ['--manifest', 'artifacts/run-manifest.json', '--require-fresh', 'verifyLite,reportEnvelope', '--result', 'artifacts/run-manifest-check.json'],
        {},
      );
      expect(check.status).toBe(0);
      const checkResult = JSON.parse(readFileSync(join(dir, 'artifacts', 'run-manifest-check.json'), 'utf8'));
      expect(checkResult.ok).toBe(true);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('fails when a required artifact is stale', () => {
    const dir = mkdtempSync(join(tmpdir(), 'run-manifest-stale-'));
    try {
      const currentCommit = 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa';
      const oldCommit = 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb';

      const verifyLitePath = join(dir, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json');
      const envelopePath = join(dir, 'artifacts', 'report-envelope.json');

      writeJson(verifyLitePath, { metadata: { gitCommit: oldCommit } });
      writeJson(envelopePath, { correlation: { commit: currentCommit } });

      const gen = runNode(
        dir,
        generateScript,
        ['--out', 'artifacts/run-manifest.json', '--top-level-command', 'unit-test'],
        { GIT_COMMIT: currentCommit },
      );
      expect(gen.status).toBe(0);

      const check = runNode(
        dir,
        checkScript,
        ['--manifest', 'artifacts/run-manifest.json', '--require-fresh', 'verifyLite', '--result', 'artifacts/run-manifest-check.json'],
        {},
      );
      expect(check.status).toBe(1);
      const checkResult = JSON.parse(readFileSync(join(dir, 'artifacts', 'run-manifest-check.json'), 'utf8'));
      expect(checkResult.ok).toBe(false);
      expect(checkResult.violations.some((v: any) => v.kind === 'stale_artifact' && v.name === 'verifyLite')).toBe(true);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
