import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const verifyScript = resolve(repoRoot, 'scripts/maintenance/remote-cleanup-post-apply-verify.mjs');
const cleanupScript = resolve(repoRoot, 'scripts/maintenance/branch-cleanup.mjs');
const moduleUrl = pathToFileURL(verifyScript).href;

const runGit = (cwd: string, args: string[]) => {
  const result = spawnSync('git', args, {
    cwd,
    encoding: 'utf8',
    timeout: 120_000,
  });
  if (result.status !== 0) {
    throw new Error(`git ${args.join(' ')} failed\nstdout=${result.stdout}\nstderr=${result.stderr}`);
  }
  return result.stdout.trim();
};

describe.sequential('remote-cleanup-post-apply-verify script', () => {
  it('verifies deleted remote refs against live remote state', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs([])).toMatchObject({
      cleanupReportJson: 'tmp/maintenance/branch-cleanup-report.json',
      outputDir: 'tmp/maintenance/remote-cleanup-post-apply-verify',
    });

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-post-apply-verify-'));
    const originDir = join(sandbox, 'origin.git');
    const repoDir = join(sandbox, 'repo');
    const approvedPath = join(sandbox, 'approved.json');
    const cleanupReportPath = join(sandbox, 'branch-cleanup-report.json');
    const outputDir = join(sandbox, 'out');

    try {
      runGit(sandbox, ['init', '--bare', originDir]);
      runGit(sandbox, ['clone', originDir, repoDir]);
      runGit(repoDir, ['config', 'user.email', 'test@example.com']);
      runGit(repoDir, ['config', 'user.name', 'Test User']);

      writeFileSync(join(repoDir, 'README.md'), 'seed\n', 'utf8');
      runGit(repoDir, ['add', 'README.md']);
      runGit(repoDir, ['commit', '-m', 'init']);
      runGit(repoDir, ['push', '-u', 'origin', 'HEAD:main']);

      runGit(repoDir, ['checkout', '-b', 'docs/stale-a']);
      writeFileSync(join(repoDir, 'stale-a.md'), 'stale\n', 'utf8');
      runGit(repoDir, ['add', 'stale-a.md']);
      runGit(repoDir, ['commit', '-m', 'docs stale a']);
      const branchOid = runGit(repoDir, ['rev-parse', 'HEAD']);
      runGit(repoDir, ['push', '-u', 'origin', 'docs/stale-a']);
      runGit(repoDir, ['checkout', 'main']);
      runGit(repoDir, ['fetch', 'origin', '--prune']);

      writeFileSync(
        approvedPath,
        `${JSON.stringify(
          {
            branches: [{ branch: 'docs/stale-a', branchOid }],
          },
          null,
          2,
        )}\n`,
      );

      const cleanup = spawnSync(
        'node',
        [
          cleanupScript,
          '--scope',
          'remote',
          '--base',
          'origin/main',
          '--remote',
          'origin',
          '--remote-branches-file',
          approvedPath,
          '--output-json',
          cleanupReportPath,
          '--apply',
        ],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );
      expect(cleanup.status, cleanup.stderr || cleanup.stdout).toBe(0);

      const result = spawnSync(
        'node',
        [verifyScript, '--cleanup-report-json', cleanupReportPath, '--output-dir', outputDir],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );
      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('deleted=1 verified=1 stillPresent=0 presentOnRemote=0 recreated=0');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.counts.reportedDeleted).toBe(1);
      expect(summary.counts.verifiedAbsent).toBe(1);
      expect(summary.counts.stillPresent).toBe(0);
      expect(summary.counts.presentOnRemote).toBe(0);
      expect(summary.counts.recreatedRefs).toBe(0);
      expect(summary.deleted).toEqual([
        expect.objectContaining({ branch: 'docs/stale-a', status: 'verified-absent' }),
      ]);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('reports still-present refs when a deleted branch still exists remotely', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-post-apply-present-'));
    const originDir = join(sandbox, 'origin.git');
    const repoDir = join(sandbox, 'repo');
    const cleanupReportPath = join(sandbox, 'branch-cleanup-report.json');
    const outputDir = join(sandbox, 'out');

    try {
      runGit(sandbox, ['init', '--bare', originDir]);
      runGit(sandbox, ['clone', originDir, repoDir]);
      runGit(repoDir, ['config', 'user.email', 'test@example.com']);
      runGit(repoDir, ['config', 'user.name', 'Test User']);

      writeFileSync(join(repoDir, 'README.md'), 'seed\n', 'utf8');
      runGit(repoDir, ['add', 'README.md']);
      runGit(repoDir, ['commit', '-m', 'init']);
      runGit(repoDir, ['push', '-u', 'origin', 'HEAD:main']);

      runGit(repoDir, ['checkout', '-b', 'docs/stale-a']);
      writeFileSync(join(repoDir, 'stale-a.md'), 'stale\n', 'utf8');
      runGit(repoDir, ['add', 'stale-a.md']);
      runGit(repoDir, ['commit', '-m', 'docs stale a']);
      const branchOid = runGit(repoDir, ['rev-parse', 'HEAD']);
      runGit(repoDir, ['push', '-u', 'origin', 'docs/stale-a']);
      runGit(repoDir, ['checkout', 'main']);
      runGit(repoDir, ['fetch', 'origin', '--prune']);

      writeFileSync(
        cleanupReportPath,
        `${JSON.stringify(
          {
            apply: true,
            scope: 'remote',
            remoteName: 'origin',
            remote: {
              selection: { mode: 'branch-list' },
              plannedDetailed: [{ branch: 'docs/stale-a', branchOid, actualOid: branchOid }],
              deleted: ['docs/stale-a'],
              failed: [],
              blocked: [],
            },
          },
          null,
          2,
        )}\n`,
      );

      const result = spawnSync(
        'node',
        [verifyScript, '--cleanup-report-json', cleanupReportPath, '--output-dir', outputDir],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.counts.reportedDeleted).toBe(1);
      expect(summary.counts.verifiedAbsent).toBe(0);
      expect(summary.counts.stillPresent).toBe(1);
      expect(summary.counts.presentOnRemote).toBe(1);
      expect(summary.counts.recreatedRefs).toBe(0);
      expect(summary.deleted).toEqual([
        expect.objectContaining({ branch: 'docs/stale-a', status: 'still-present', expectedOid: branchOid, actualOid: branchOid }),
      ]);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('reports recreated refs when the branch name reappears at a different OID', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-post-apply-recreated-'));
    const originDir = join(sandbox, 'origin.git');
    const repoDir = join(sandbox, 'repo');
    const cleanupReportPath = join(sandbox, 'branch-cleanup-report.json');
    const outputDir = join(sandbox, 'out');

    try {
      runGit(sandbox, ['init', '--bare', originDir]);
      runGit(sandbox, ['clone', originDir, repoDir]);
      runGit(repoDir, ['config', 'user.email', 'test@example.com']);
      runGit(repoDir, ['config', 'user.name', 'Test User']);

      writeFileSync(join(repoDir, 'README.md'), 'seed\n', 'utf8');
      runGit(repoDir, ['add', 'README.md']);
      runGit(repoDir, ['commit', '-m', 'init']);
      runGit(repoDir, ['push', '-u', 'origin', 'HEAD:main']);

      runGit(repoDir, ['checkout', '-b', 'docs/stale-a']);
      writeFileSync(join(repoDir, 'stale-a.md'), 'stale\n', 'utf8');
      runGit(repoDir, ['add', 'stale-a.md']);
      runGit(repoDir, ['commit', '-m', 'docs stale a']);
      const originalOid = runGit(repoDir, ['rev-parse', 'HEAD']);
      runGit(repoDir, ['push', '-u', 'origin', 'docs/stale-a']);
      runGit(repoDir, ['checkout', 'main']);
      runGit(repoDir, ['branch', '-D', 'docs/stale-a']);

      runGit(repoDir, ['checkout', '-b', 'docs/stale-a']);
      writeFileSync(join(repoDir, 'stale-a.md'), 'recreated\n', 'utf8');
      runGit(repoDir, ['add', 'stale-a.md']);
      runGit(repoDir, ['commit', '-m', 'docs stale a recreated']);
      const recreatedOid = runGit(repoDir, ['rev-parse', 'HEAD']);
      expect(recreatedOid).not.toBe(originalOid);
      runGit(repoDir, ['push', '--force', '-u', 'origin', 'docs/stale-a']);
      runGit(repoDir, ['checkout', 'main']);
      runGit(repoDir, ['fetch', 'origin', '--prune']);

      writeFileSync(
        cleanupReportPath,
        `${JSON.stringify(
          {
            apply: true,
            scope: 'remote',
            remoteName: 'origin',
            remote: {
              selection: { mode: 'branch-list' },
              plannedDetailed: [{ branch: 'docs/stale-a', branchOid: originalOid, actualOid: originalOid }],
              deleted: ['docs/stale-a'],
              failed: [],
              blocked: [],
            },
          },
          null,
          2,
        )}\n`,
      );

      const result = spawnSync(
        'node',
        [verifyScript, '--cleanup-report-json', cleanupReportPath, '--output-dir', outputDir],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );
      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('stillPresent=0 presentOnRemote=1 recreated=1');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.counts.reportedDeleted).toBe(1);
      expect(summary.counts.verifiedAbsent).toBe(0);
      expect(summary.counts.stillPresent).toBe(0);
      expect(summary.counts.presentOnRemote).toBe(1);
      expect(summary.counts.recreatedRefs).toBe(1);
      expect(summary.deleted).toEqual([
        expect.objectContaining({
          branch: 'docs/stale-a',
          status: 'recreated-ref',
          expectedOid: originalOid,
          actualOid: recreatedOid,
        }),
      ]);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects dry-run or local-only cleanup reports', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-post-apply-invalid-'));
    const repoDir = join(sandbox, 'repo');
    const cleanupReportPath = join(sandbox, 'branch-cleanup-report.json');
    const outputDir = join(sandbox, 'out');

    try {
      mkdirSync(repoDir, { recursive: true });
      runGit(repoDir, ['init', '-b', 'main']);
      runGit(repoDir, ['config', 'user.email', 'test@example.com']);
      runGit(repoDir, ['config', 'user.name', 'Test User']);
      writeFileSync(join(repoDir, 'README.md'), 'seed\n', 'utf8');
      runGit(repoDir, ['add', 'README.md']);
      runGit(repoDir, ['commit', '-m', 'init']);

      writeFileSync(
        cleanupReportPath,
        `${JSON.stringify(
          {
            apply: false,
            scope: 'local',
            remoteName: 'origin',
            remote: {},
          },
          null,
          2,
        )}\n`,
      );

      const result = spawnSync(
        'node',
        [verifyScript, '--cleanup-report-json', cleanupReportPath, '--output-dir', outputDir],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );
      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('cleanup report must be an apply run');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
