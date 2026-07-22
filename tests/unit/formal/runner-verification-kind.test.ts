import { describe, expect, it } from 'vitest';
import { chmodSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { dirname, delimiter, join, resolve } from 'node:path';

const repoRoot = resolve('.');
const localTmpRoot = resolve(repoRoot, '.codex-local/tmp');

function writeExecutable(target: string, content: string) {
  mkdirSync(dirname(target), { recursive: true });
  writeFileSync(target, content, 'utf8');
  chmodSync(target, 0o755);
}

function runRunner(cwd: string, script: string, env: NodeJS.ProcessEnv) {
  return spawnSync(process.execPath, [resolve(repoRoot, script)], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env, ...env },
  });
}

describe('reviewed runner verificationKind binding', () => {
  it('keeps Kani presence detection ineligible for proof claims', () => {
    mkdirSync(localTmpRoot, { recursive: true });
    const sandbox = mkdtempSync(join(localTmpRoot, 'kani-kind-'));
    try {
      const bin = join(sandbox, 'bin');
      writeExecutable(join(bin, 'kani'), `#!/bin/sh
printf '%s\n' 'kani 0.65.0'
exit 0
`);
      const result = runRunner(sandbox, 'scripts/formal/verify-kani.mjs', {
        PATH: `${bin}${delimiter}${process.env.PATH || ''}`,
      });
      expect(result.status, result.stderr || result.stdout).toBe(0);
      const summary = JSON.parse(readFileSync(
        join(sandbox, 'artifacts/hermetic-reports/formal/kani-summary.json'),
        'utf8',
      ));
      expect(summary.runnerResult.executionEvidence).toMatchObject({
        verificationKind: 'presence',
        executionOccurred: false,
        result: { status: 'skipped', code: null },
      });
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('keeps a successful Lean lake build ineligible for proof claims', () => {
    mkdirSync(localTmpRoot, { recursive: true });
    const sandbox = mkdtempSync(join(localTmpRoot, 'lean-kind-'));
    try {
      mkdirSync(join(sandbox, 'spec/lean'), { recursive: true });
      const bin = join(sandbox, 'bin');
      writeExecutable(join(bin, 'lake'), `#!/bin/sh
if [ "$1" = "--version" ]; then
  printf '%s\n' 'Lake version 5.0.0 (Lean version 4.19.0)'
fi
exit 0
`);
      const result = runRunner(sandbox, 'scripts/formal/verify-lean.mjs', {
        PATH: `${bin}${delimiter}${process.env.PATH || ''}`,
      });
      expect(result.status, result.stderr || result.stdout).toBe(0);
      const summary = JSON.parse(readFileSync(
        join(sandbox, 'artifacts/hermetic-reports/formal/lean-summary.json'),
        'utf8',
      ));
      expect(summary.runnerResult.executionEvidence).toMatchObject({
        verificationKind: 'build',
        executionOccurred: true,
        result: { status: 'ok', code: 0 },
      });
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
