import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const branchInventoryScript = resolve(repoRoot, 'scripts/maintenance/branch-inventory.mjs');
const branchInventoryModuleUrl = pathToFileURL(branchInventoryScript).href;

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

describe.sequential('branch-inventory script', () => {
  it('collects PR-merged local branch candidates without touching linked worktrees', async () => {
    const mod = await import(branchInventoryModuleUrl);
    const localRefs = [
      { name: 'main', oid: 'mainoid' },
      { name: 'feat/pr-merged', oid: 'abc123' },
      { name: 'feat/pr-merged-reused', oid: 'local-tip' },
      { name: 'feat/already-merged', oid: 'mergedoid' },
      { name: 'feat/in-worktree', oid: 'worktreeoid' },
      { name: 'release/1.0', oid: 'releaseoid' },
    ];
    const mergedLocal = new Set(['main', 'feat/already-merged']);
    const mergedPullRequests = {
      byHeadRefName: new Map([
        [
          'feat/pr-merged',
          [
            {
              number: 2463,
              mergedAt: '2026-03-06T10:00:00Z',
              url: 'https://example.invalid/pr/2463',
              headRefOid: 'abc123',
            },
          ],
        ],
        [
          'feat/pr-merged-reused',
          [
            {
              number: 2462,
              mergedAt: '2026-03-05T10:00:00Z',
              url: 'https://example.invalid/pr/2462',
              headRefOid: 'old-tip',
            },
          ],
        ],
      ]),
    };

    const result = mod.collectLocalPrMergedCandidates(
      localRefs,
      {
        currentBranch: 'main',
        mergedLocal,
        linkedWorktreeBranches: [{ branch: 'feat/in-worktree', path: '/repo-wt' }],
      },
      { mergedPullRequests },
    );

    expect(result).toEqual([
      {
        branch: 'feat/pr-merged',
        number: 2463,
        mergedAt: '2026-03-06T10:00:00Z',
        url: 'https://example.invalid/pr/2463',
        headRefOid: 'abc123',
      },
    ]);
  });

  it('filters merged PR inventory by configured base branch and groups by head ref', async () => {
    const mod = await import(branchInventoryModuleUrl);
    const result = mod.loadMergedPullRequests(
      {
        limit: 50,
        baseBranch: 'main',
      },
      {
        ghRunner: () => ({
          ok: true,
          output: JSON.stringify([
            {
              number: 1,
              title: 'keep',
              url: 'https://example.invalid/pr/1',
              mergedAt: '2026-03-06T10:00:00Z',
              headRefName: 'feat/keep',
              headRefOid: 'sha-keep',
              baseRefName: 'main',
            },
            {
              number: 2,
              title: 'drop',
              url: 'https://example.invalid/pr/2',
              mergedAt: '2026-03-06T09:00:00Z',
              headRefName: 'feat/keep',
              headRefOid: 'sha-old',
              baseRefName: 'release/1.0',
            },
          ]),
        }),
      },
    );

    expect(result.available).toBe(true);
    expect(result.requestedBaseBranch).toBe('main');
    expect(result.requestedLimit).toBe(50);
    expect(result.items).toHaveLength(1);
    expect(result.byHeadRefName.get('feat/keep')).toEqual([
      expect.objectContaining({ number: 1, headRefOid: 'sha-keep', baseRefName: 'main' }),
    ]);
  });

  it('collects detached clean worktrees on base separately from linked branches', async () => {
    const mod = await import(branchInventoryModuleUrl);
    const result = mod.collectWorktreeInventory(
      [
        { path: '/repo', branch: 'main', detached: false, prunable: false, locked: false, head: '1111111' },
        {
          path: '/repo-wt-branch',
          branch: 'feat/in-worktree',
          detached: false,
          prunable: false,
          locked: false,
          head: '2222222',
        },
        {
          path: '/repo-wt-detached-clean',
          branch: '',
          detached: true,
          prunable: false,
          locked: false,
          head: '3333333',
        },
        {
          path: '/repo-wt-detached-dirty',
          branch: '',
          detached: true,
          prunable: false,
          locked: false,
          head: '4444444',
        },
      ],
      {
        currentWorktreePath: '/repo',
        baseRef: 'origin/main',
      },
      {
        getStatus: (worktreePath: string) =>
          worktreePath.endsWith('dirty')
            ? { ok: true, output: ' M README.md' }
            : { ok: true, output: '' },
        isCommitOnBase: (commit: string) => commit === '3333333',
      },
    );

    expect(result.linkedBranches).toEqual([{ branch: 'feat/in-worktree', path: '/repo-wt-branch' }]);
    expect(result.detachedOnBaseClean).toEqual([
      { head: '3333333', path: '/repo-wt-detached-clean' },
    ]);
    expect(result.skippedDetached).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ path: '/repo-wt-detached-dirty', reason: 'dirty-worktree' }),
      ]),
    );
  });

  it('includes remote candidate OIDs in detailed inventory sections', async () => {
    const mod = await import(branchInventoryModuleUrl);
    const gitRunner = (args: string[]) => {
      const key = args.join(' ');
      if (key === 'branch --show-current') return 'main';
      if (key === 'rev-parse --show-toplevel') return '/repo';
      if (
        key ===
        'for-each-ref refs/heads --format=%(refname:short)\t%(committerdate:iso8601)\t%(committerdate:unix)\t%(upstream:short)\t%(objectname)'
      ) {
        return 'main\t2026-03-07 00:00:00 +0900\t1772818800\t\tmainoid';
      }
      if (
        key ===
        'for-each-ref refs/remotes/origin --format=%(refname:short)\t%(committerdate:iso8601)\t%(committerdate:unix)\t%(upstream:short)\t%(objectname)'
      ) {
        return [
          'origin/HEAD\t2026-03-07 00:00:00 +0900\t1772818800\t\tmainoid',
          'origin/main\t2026-03-07 00:00:00 +0900\t1772818800\t\tmainoid',
          'origin/feat/remote-merged\t2026-03-06 00:00:00 +0900\t1772732400\t\toid-merged',
          'origin/docs/remote-stale\t2026-02-20 00:00:00 +0900\t1771513200\t\toid-stale',
        ].join('\n');
      }
      if (key === 'worktree list --porcelain') {
        return 'worktree /repo\nHEAD mainoid\nbranch refs/heads/main\n';
      }
      if (key === 'branch --format=%(refname:short) --merged origin/main') {
        return 'main';
      }
      if (key === 'branch -r --format=%(refname:short) --merged origin/main') {
        return ['origin/main', 'origin/feat/remote-merged'].join('\n');
      }
      throw new Error(`Unexpected git command: ${key}`);
    };

    const report = mod.buildInventoryReport(
      {
        base: 'origin/main',
        remote: 'origin',
        outputJson: 'tmp/maintenance/branch-inventory.json',
        outputMd: 'tmp/maintenance/branch-inventory.md',
        staleDays: 7,
        top: 10,
        ghPrLimit: 1000,
        ghPrBase: '',
      },
      {
        nowUnix: 1772905200,
        generatedAt: '2026-03-07T03:00:00Z',
        gitRunner,
        mergedPullRequestsLoader: () => ({
          available: false,
          reason: 'disabled',
          requestedBaseBranch: 'main',
          requestedLimit: 1000,
          items: [],
          byHeadRefName: new Map(),
        }),
      },
    );

    expect(report.candidates.remoteMerged).toEqual(['feat/remote-merged']);
    expect(report.candidates.remoteMergedDetailed).toEqual([
      { branch: 'feat/remote-merged', oid: 'oid-merged' },
    ]);
    expect(report.candidates.remoteStaleByAge).toEqual([
      expect.objectContaining({ branch: 'docs/remote-stale' }),
    ]);
    expect(report.candidates.remoteStaleByAgeDetailed).toEqual([
      expect.objectContaining({ branch: 'docs/remote-stale', oid: 'oid-stale' }),
    ]);
  });

  it('writes inventory report with linked branches and detached base worktrees', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-branch-inventory-'));
    const repoDir = join(sandbox, 'repo');
    const wtBranchDir = join(sandbox, 'wt-branch');
    const wtDetachedDir = join(sandbox, 'wt-detached');
    const reportJson = join(sandbox, 'branch-inventory.json');
    const reportMd = join(sandbox, 'branch-inventory.md');

    try {
      mkdirSync(repoDir, { recursive: true });
      runGit(repoDir, ['init', '-b', 'main']);
      runGit(repoDir, ['config', 'user.email', 'test@example.com']);
      runGit(repoDir, ['config', 'user.name', 'Test User']);

      writeFileSync(join(repoDir, 'README.md'), 'seed\n', 'utf8');
      runGit(repoDir, ['add', 'README.md']);
      runGit(repoDir, ['commit', '-m', 'init']);

      runGit(repoDir, ['checkout', '-b', 'feat/in-worktree']);
      writeFileSync(join(repoDir, 'feature.txt'), 'feature\n', 'utf8');
      runGit(repoDir, ['add', 'feature.txt']);
      runGit(repoDir, ['commit', '-m', 'feature']);
      runGit(repoDir, ['checkout', 'main']);

      runGit(repoDir, ['worktree', 'add', wtBranchDir, 'feat/in-worktree']);
      runGit(repoDir, ['worktree', 'add', '--detach', wtDetachedDir, 'HEAD']);

      const result = spawnSync(
        'node',
        [
          branchInventoryScript,
          '--base',
          'main',
          '--output-json',
          reportJson,
          '--output-md',
          reportMd,
        ],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);

      const report = JSON.parse(readFileSync(reportJson, 'utf8'));
      expect(report.ghMergedPullRequests.available).toBe(false);
      expect(report.counts.linkedWorktreeBranches).toBe(1);
      expect(report.counts.detachedWorktreesOnBaseClean).toBe(1);
      expect(report.candidates.linkedWorktreeBranches).toEqual([
        { branch: 'feat/in-worktree', path: wtBranchDir },
      ]);
      expect(report.candidates.detachedWorktreesOnBaseClean).toEqual([
        expect.objectContaining({ path: wtDetachedDir }),
      ]);

      const markdown = readFileSync(reportMd, 'utf8');
      expect(markdown).toContain('Linked worktree branches (excluded from cleanup)');
      expect(markdown).toContain('Detached clean worktrees whose HEAD is on base (manual review only)');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
