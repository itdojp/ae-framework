import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const branchCleanupScript = resolve(repoRoot, 'scripts/maintenance/branch-cleanup.mjs');
const branchCleanupModuleUrl = pathToFileURL(branchCleanupScript).href;

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

describe.sequential('branch-cleanup script', () => {
  it('rejects fail-open reviewed input arguments', async () => {
    const mod = await import(branchCleanupModuleUrl);

    expect(() => mod.parseArgs(['--scope', 'remote', '--remote-manifest-json', ''])).toThrow(
      '--remote-manifest-json requires a non-empty value',
    );
    expect(() =>
      mod.parseArgs(['--scope', 'remote', '--remote-branches-file', '--apply']),
    ).toThrow('--remote-branches-file requires a non-empty value');
    expect(() => mod.parseArgs(['--scope', 'remote', '--remote-manifest-mode', 'merged'])).toThrow(
      '--remote-manifest-mode requires --remote-manifest-json',
    );
  });

  it('parses reviewed branch lists from text and JSON input', async () => {
    const mod = await import(branchCleanupModuleUrl);

    expect(
      mod.parseRemoteBranchesFile(
        ['# comment', 'docs/alpha', '  ', 'docs/beta'].join('\n'),
      ),
    ).toEqual([
      expect.objectContaining({ branch: 'docs/alpha', selectionMode: 'branch-list' }),
      expect.objectContaining({ branch: 'docs/beta', selectionMode: 'branch-list' }),
    ]);

    expect(
      mod.parseRemoteBranchesFile(
        JSON.stringify({
          branches: [{ branch: 'docs/gamma', branchOid: 'oid-gamma' }],
        }),
      ),
    ).toEqual([
      expect.objectContaining({
        branch: 'docs/gamma',
        branchOid: 'oid-gamma',
        selectionMode: 'branch-list',
      }),
    ]);
  });

  it('applies merged checks only to merged-safety modes and blocks OID mismatch', async () => {
    const mod = await import(branchCleanupModuleUrl);

    const mergedPlan = mod.collectRemoteCleanupPlan({
      entries: [
        { branch: 'docs/merged-ok', branchOid: 'oid-1' },
        { branch: 'docs/merged-mismatch', branchOid: 'oid-old' },
        { branch: 'docs/stale-review', branchOid: 'oid-3' },
        { branch: 'release/1.0', branchOid: 'oid-release' },
      ],
      remoteName: 'origin',
      mergedRemoteRefs: new Set(['origin/docs/merged-ok', 'origin/docs/merged-mismatch']),
      remoteRefOids: new Map([
        ['docs/merged-ok', 'oid-1'],
        ['docs/merged-mismatch', 'oid-new'],
        ['docs/stale-review', 'oid-3'],
        ['release/1.0', 'oid-release'],
      ]),
      max: 10,
      selectionMode: 'triage-merged',
      sourcePath: '/tmp/remote-branch-triage.json',
      expectedBase: 'origin/main',
      expectedRemote: 'origin',
    });

    expect(mergedPlan.planned).toEqual(['docs/merged-ok']);
    expect(mergedPlan.blocked).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ branch: 'docs/merged-mismatch', reason: 'oid-mismatch' }),
        expect.objectContaining({ branch: 'docs/stale-review', reason: 'not-merged-to-base' }),
        expect.objectContaining({ branch: 'release/1.0', reason: 'protected-branch' }),
      ]),
    );

    const reviewedPlan = mod.collectRemoteCleanupPlan({
      entries: [{ branch: 'docs/stale-review', branchOid: 'oid-3' }],
      remoteName: 'origin',
      mergedRemoteRefs: new Set(),
      remoteRefOids: new Map([['docs/stale-review', 'oid-3']]),
      max: 10,
      selectionMode: 'branch-list',
      sourcePath: '/tmp/approved-branches.txt',
      expectedBase: '',
      expectedRemote: '',
    });

    expect(reviewedPlan.planned).toEqual(['docs/stale-review']);
    expect(reviewedPlan.blocked).toEqual([]);
  });

  it('uses reviewed triage manifest rows instead of generic remote merged candidates during dry-run', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-branch-cleanup-'));
    const originDir = join(sandbox, 'origin.git');
    const repoDir = join(sandbox, 'repo');
    const reportPath = join(sandbox, 'branch-cleanup-report.json');
    const triagePath = join(sandbox, 'remote-branch-triage.json');

    try {
      runGit(sandbox, ['init', '--bare', originDir]);
      runGit(sandbox, ['clone', originDir, repoDir]);

      runGit(repoDir, ['config', 'user.email', 'test@example.com']);
      runGit(repoDir, ['config', 'user.name', 'Test User']);

      writeFileSync(join(repoDir, 'README.md'), 'seed\n', 'utf8');
      runGit(repoDir, ['add', 'README.md']);
      runGit(repoDir, ['commit', '-m', 'init']);
      runGit(repoDir, ['push', '-u', 'origin', 'HEAD:main']);

      runGit(repoDir, ['checkout', '-b', 'docs/merged-a']);
      writeFileSync(join(repoDir, 'merged-a.md'), 'A\n', 'utf8');
      runGit(repoDir, ['add', 'merged-a.md']);
      runGit(repoDir, ['commit', '-m', 'docs merged a']);
      runGit(repoDir, ['push', '-u', 'origin', 'docs/merged-a']);
      runGit(repoDir, ['checkout', 'main']);
      runGit(repoDir, ['merge', '--ff-only', 'docs/merged-a']);
      runGit(repoDir, ['push', 'origin', 'main']);

      runGit(repoDir, ['checkout', '-b', 'docs/merged-b']);
      writeFileSync(join(repoDir, 'merged-b.md'), 'B\n', 'utf8');
      runGit(repoDir, ['add', 'merged-b.md']);
      runGit(repoDir, ['commit', '-m', 'docs merged b']);
      runGit(repoDir, ['push', '-u', 'origin', 'docs/merged-b']);
      const mergedBOid = runGit(repoDir, ['rev-parse', 'HEAD']);
      runGit(repoDir, ['checkout', 'main']);
      runGit(repoDir, ['merge', '--ff-only', 'docs/merged-b']);
      runGit(repoDir, ['push', 'origin', 'main']);
      runGit(repoDir, ['fetch', 'origin', '--prune']);

      writeFileSync(
        triagePath,
        `${JSON.stringify(
          {
            sourceInventory: {
              remote: 'origin',
              base: 'origin/main',
            },
            remoteMerged: [
              {
                branch: 'docs/merged-b',
                branchOid: mergedBOid,
                deleteCommand: 'git push origin --delete docs/merged-b',
              },
            ],
            remoteStale: [],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync(
        'node',
        [
          branchCleanupScript,
          '--base',
          'origin/main',
          '--scope',
          'remote',
          '--remote-manifest-json',
          triagePath,
          '--remote-manifest-mode',
          'merged',
          '--output-json',
          reportPath,
        ],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('remote selection=triage-merged blocked=0');
      expect(result.stdout).toContain('DRYRUN remote: git push origin --delete docs/merged-b');
      expect(result.stdout).not.toContain('docs/merged-a');

      const report = JSON.parse(readFileSync(reportPath, 'utf8'));
      expect(report.remote.selection).toEqual({
        mode: 'triage-merged',
        sourcePath: resolve(triagePath),
        expectedBase: 'origin/main',
        expectedRemote: 'origin',
      });
      expect(report.remote.plannedDetailed).toEqual([
        expect.objectContaining({
          branch: 'docs/merged-b',
          branchOid: mergedBOid,
          actualOid: mergedBOid,
          selectionMode: 'triage-merged',
        }),
      ]);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('refreshes origin before local cleanup analysis when --fetch is set', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-branch-cleanup-fetch-'));
    const originDir = join(sandbox, 'origin.git');
    const repoDir = join(sandbox, 'repo');
    const reportPath = join(sandbox, 'branch-cleanup-report.json');

    try {
      runGit(sandbox, ['init', '--bare', originDir]);
      runGit(sandbox, ['clone', originDir, repoDir]);

      runGit(repoDir, ['config', 'user.email', 'test@example.com']);
      runGit(repoDir, ['config', 'user.name', 'Test User']);

      writeFileSync(join(repoDir, 'README.md'), 'seed\n', 'utf8');
      runGit(repoDir, ['add', 'README.md']);
      runGit(repoDir, ['commit', '-m', 'init']);
      runGit(repoDir, ['push', '-u', 'origin', 'HEAD:main']);

      runGit(repoDir, ['checkout', '-b', 'docs/merged-a']);
      writeFileSync(join(repoDir, 'merged-a.md'), 'A\n', 'utf8');
      runGit(repoDir, ['add', 'merged-a.md']);
      runGit(repoDir, ['commit', '-m', 'docs merged a']);
      runGit(repoDir, ['push', '-u', 'origin', 'docs/merged-a']);
      runGit(repoDir, ['checkout', 'main']);
      runGit(repoDir, ['merge', '--ff-only', 'docs/merged-a']);
      runGit(repoDir, ['push', 'origin', 'main']);

      const result = spawnSync(
        'node',
        [
          branchCleanupScript,
          '--base',
          'origin/main',
          '--scope',
          'local',
          '--fetch',
          '--output-json',
          reportPath,
        ],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('fetch=ok remote=origin');
      expect(result.stdout).toContain('DRYRUN local: git branch -d docs/merged-a');

      const report = JSON.parse(readFileSync(reportPath, 'utf8'));
      expect(report.fetch).toEqual({
        attempted: true,
        ok: true,
        remote: 'origin',
        output: '',
      });
      expect(report.local.planned).toEqual(['docs/merged-a']);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects reviewed manifests that do not record remote/base provenance', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-branch-cleanup-invalid-manifest-'));
    const repoDir = join(sandbox, 'repo');
    const reportPath = join(sandbox, 'branch-cleanup-report.json');
    const triagePath = join(sandbox, 'remote-branch-triage.json');

    try {
      mkdirSync(repoDir, { recursive: true });
      runGit(repoDir, ['init', '-b', 'main']);
      runGit(repoDir, ['config', 'user.email', 'test@example.com']);
      runGit(repoDir, ['config', 'user.name', 'Test User']);

      writeFileSync(join(repoDir, 'README.md'), 'seed\n', 'utf8');
      runGit(repoDir, ['add', 'README.md']);
      runGit(repoDir, ['commit', '-m', 'init']);

      writeFileSync(
        triagePath,
        `${JSON.stringify(
          {
            remoteMerged: [{ branch: 'docs/merged-b', branchOid: 'oid-1' }],
            remoteStale: [],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync(
        'node',
        [
          branchCleanupScript,
          '--base',
          'main',
          '--scope',
          'remote',
          '--remote-manifest-json',
          triagePath,
          '--output-json',
          reportPath,
        ],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('remote manifest is missing sourceInventory.remote/base');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
