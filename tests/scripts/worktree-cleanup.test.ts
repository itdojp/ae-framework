import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const worktreeCleanupScript = resolve(repoRoot, 'scripts/maintenance/worktree-cleanup.mjs');
const worktreeCleanupModuleUrl = pathToFileURL(worktreeCleanupScript).href;

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

describe.sequential('worktree-cleanup script', () => {
  it('parses porcelain output and filters candidates by merged/protected rules', async () => {
    const mod = await import(worktreeCleanupModuleUrl);
    const raw = [
      'worktree /repo',
      'HEAD 1111111',
      'branch refs/heads/main',
      'worktree /repo-wt-feature',
      'HEAD 2222222',
      'branch refs/heads/feat/merged',
      'worktree /repo-wt-release',
      'HEAD 3333333',
      'branch refs/heads/release/1.0',
      '',
    ].join('\n');

    const worktrees = mod.parseWorktreePorcelain(raw);
    const result = mod.collectCleanupCandidates(
      worktrees,
      {
        currentWorktreePath: '/repo',
        baseRef: 'origin/main',
      },
      {
        branchExists: () => true,
        isMergedToBase: (branch: string) => branch === 'feat/merged',
      },
    );

    expect(result.candidates).toEqual([{ path: '/repo-wt-feature', branch: 'feat/merged' }]);
    expect(result.skipped).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ path: '/repo', reason: 'current-worktree' }),
        expect.objectContaining({ path: '/repo-wt-release', reason: 'protected-branch' }),
      ]),
    );
  });

  it('dry-run prints only removable worktree and writes report', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-worktree-cleanup-'));
    const repoDir = join(sandbox, 'repo');
    const wtMergedDir = join(sandbox, 'wt-merged');
    const wtProtectedDir = join(sandbox, 'wt-protected');
    const reportPath = join(sandbox, 'worktree-cleanup-report.json');

    try {
      mkdirSync(repoDir, { recursive: true });
      runGit(repoDir, ['init', '-b', 'main']);
      runGit(repoDir, ['config', 'user.email', 'test@example.com']);
      runGit(repoDir, ['config', 'user.name', 'Test User']);

      writeFileSync(join(repoDir, 'README.md'), 'seed\n', 'utf8');
      runGit(repoDir, ['add', 'README.md']);
      runGit(repoDir, ['commit', '-m', 'init']);

      runGit(repoDir, ['checkout', '-b', 'feat/merged']);
      writeFileSync(join(repoDir, 'feature.txt'), 'feature\n', 'utf8');
      runGit(repoDir, ['add', 'feature.txt']);
      runGit(repoDir, ['commit', '-m', 'feat']);
      runGit(repoDir, ['checkout', 'main']);
      runGit(repoDir, ['merge', '--ff-only', 'feat/merged']);

      runGit(repoDir, ['branch', 'release/1.0']);
      runGit(repoDir, ['worktree', 'add', wtMergedDir, 'feat/merged']);
      runGit(repoDir, ['worktree', 'add', wtProtectedDir, 'release/1.0']);

      const result = spawnSync(
        'node',
        [worktreeCleanupScript, '--base', 'main', '--output-json', reportPath],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain(`DRYRUN: git worktree remove "${wtMergedDir}"`);
      expect(result.stdout).not.toContain(`DRYRUN: git worktree remove "${wtProtectedDir}"`);

      const report = JSON.parse(readFileSync(reportPath, 'utf8'));
      expect(report.counts.candidates).toBe(1);
      expect(report.planned).toEqual([{ path: wtMergedDir, branch: 'feat/merged' }]);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
