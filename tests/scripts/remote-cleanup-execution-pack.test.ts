import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/maintenance/remote-cleanup-execution-pack.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

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

describe.sequential('remote-cleanup-execution-pack script', () => {
  it('renders a self-contained execution pack and dry-run report from delete-ready review status', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs([])).toMatchObject({
      reviewStatusDir: 'tmp/maintenance/remote-cleanup-review-status',
      outputDir: 'tmp/maintenance/remote-cleanup-execution-pack',
      base: 'origin/main',
      remote: 'origin',
      max: 100,
    });

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-execution-pack-'));
    const originDir = join(sandbox, 'origin.git');
    const repoDir = join(sandbox, 'repo');
    const reviewStatusDir = join(sandbox, 'review-status');
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
      runGit(repoDir, ['push', '-u', 'origin', 'docs/stale-a']);
      const branchOid = runGit(repoDir, ['rev-parse', 'HEAD']);
      runGit(repoDir, ['checkout', 'main']);
      runGit(repoDir, ['fetch', 'origin', '--prune']);

      mkdirSync(reviewStatusDir, { recursive: true });
      const reviewedManifestPath = join(reviewStatusDir, 'reviewed-triage.json');
      writeFileSync(
        reviewedManifestPath,
        `${JSON.stringify(
          {
            sourceInventory: {
              path: '/tmp/remote-branch-triage.json',
              generatedAt: '2026-03-08T00:00:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            reviewedDecisions: {
              sourceTriagePath: '/tmp/remote-branch-triage.json',
              generatedAt: '2026-03-08T00:05:00Z',
            },
            remoteStale: [
              {
                branch: 'docs/stale-a',
                branchOid,
                decision: 'delete',
                notes: 'approved',
                prState: 'merged',
              },
            ],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(reviewStatusDir, 'summary.json'),
        `${JSON.stringify(
          {
            generatedAt: '2026-03-08T00:10:00Z',
            source: {
              reviewedManifestPath,
              referenceAuditDir: join(reviewStatusDir, 'audit'),
              sourceTriagePath: '/tmp/remote-branch-triage.json',
            },
            overall: {
              'delete-ready': 1,
            },
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(reviewStatusDir, 'delete-ready.json'),
        `${JSON.stringify(
          [
            {
              branch: 'docs/stale-a',
              branchOid,
              decision: 'delete',
              prState: 'merged',
              batchId: 'B',
              notes: 'approved',
            },
          ],
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(reviewStatusDir, 'delete-ready.branches.json'),
        `${JSON.stringify(
          {
            branches: [{ branch: 'docs/stale-a', branchOid, decision: 'delete', prState: 'merged' }],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync(
        'node',
        [scriptPath, '--review-status-dir', reviewStatusDir, '--output-dir', outputDir, '--base', 'origin/main', '--remote', 'origin'],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('delete-ready=1 planned=1 blocked=0');

      const approvedBranchList = JSON.parse(readFileSync(join(outputDir, 'approved-remote-branches.json'), 'utf8'));
      expect(approvedBranchList.sourceInventory).toMatchObject({
        base: 'origin/main',
        remote: 'origin',
      });
      expect(approvedBranchList.branches).toEqual([
        { branch: 'docs/stale-a', branchOid, decision: 'delete', prState: 'merged' },
      ]);

      const dryRunReport = JSON.parse(readFileSync(join(outputDir, 'branch-cleanup-dry-run-report.json'), 'utf8'));
      expect(dryRunReport.remote.plannedDetailed).toEqual([
        expect.objectContaining({
          branch: 'docs/stale-a',
          branchOid,
          actualOid: branchOid,
          selectionMode: 'branch-list',
        }),
      ]);

      const commands = readFileSync(join(outputDir, 'commands.sh'), 'utf8');
      expect(commands).toContain('approved-remote-branches.json');
      expect(commands).toContain('--apply');

      const issueComment = readFileSync(join(outputDir, 'issue-comment.md'), 'utf8');
      expect(issueComment).toContain('delete-ready rows: 1');
      expect(issueComment).toContain('this step does not delete remote branches');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects reviewed manifest base or remote mismatches', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-execution-pack-invalid-'));
    const reviewStatusDir = join(sandbox, 'review-status');
    const outputDir = join(sandbox, 'out');
    const reviewedManifestPath = join(reviewStatusDir, 'reviewed-triage.json');

    try {
      mkdirSync(reviewStatusDir, { recursive: true });
      writeFileSync(
        reviewedManifestPath,
        `${JSON.stringify(
          {
            sourceInventory: {
              base: 'origin/release',
              remote: 'origin',
            },
            reviewedDecisions: {
              sourceTriagePath: '/tmp/remote-branch-triage.json',
            },
            remoteStale: [],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(reviewStatusDir, 'summary.json'),
        `${JSON.stringify(
          {
            source: {
              reviewedManifestPath,
              sourceTriagePath: '/tmp/remote-branch-triage.json',
            },
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(join(reviewStatusDir, 'delete-ready.json'), '[]\n', 'utf8');
      writeFileSync(join(reviewStatusDir, 'delete-ready.branches.json'), '{"branches":[{"branch":"docs/stale-a"}]}\n', 'utf8');

      const result = spawnSync(
        'node',
        [scriptPath, '--review-status-dir', reviewStatusDir, '--output-dir', outputDir, '--base', 'origin/main', '--remote', 'origin'],
        {
          cwd: repoRoot,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('reviewed manifest base mismatch');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects empty delete-ready branch lists', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-execution-pack-empty-'));
    const reviewStatusDir = join(sandbox, 'review-status');
    const outputDir = join(sandbox, 'out');
    const reviewedManifestPath = join(reviewStatusDir, 'reviewed-triage.json');

    try {
      mkdirSync(reviewStatusDir, { recursive: true });
      writeFileSync(
        reviewedManifestPath,
        `${JSON.stringify(
          {
            sourceInventory: {
              base: 'origin/main',
              remote: 'origin',
            },
            reviewedDecisions: {
              sourceTriagePath: '/tmp/remote-branch-triage.json',
            },
            remoteStale: [],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(reviewStatusDir, 'summary.json'),
        `${JSON.stringify(
          {
            source: {
              reviewedManifestPath,
              sourceTriagePath: '/tmp/remote-branch-triage.json',
            },
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(join(reviewStatusDir, 'delete-ready.json'), '[]\n', 'utf8');
      writeFileSync(join(reviewStatusDir, 'delete-ready.branches.json'), '{"branches":[]}\n', 'utf8');

      const result = spawnSync('node', [scriptPath, '--review-status-dir', reviewStatusDir, '--output-dir', outputDir], {
        cwd: repoRoot,
        encoding: 'utf8',
        timeout: 120_000,
      });

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('delete-ready branch list is empty');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
