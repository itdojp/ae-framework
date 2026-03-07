import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/maintenance/remote-cleanup-reference-audit.mjs');
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

describe.sequential('remote-cleanup-reference-audit script', () => {
  it('classifies repo paths and scans references by category', async () => {
    const mod = await import(moduleUrl);

    expect(mod.classifyRepoPath('.github/workflows/test.yml')).toBe('automation');
    expect(mod.classifyRepoPath('scripts/maintenance/test.mjs')).toBe('automation');
    expect(mod.classifyRepoPath('docs/plan.md')).toBe('plan');
    expect(mod.classifyRepoPath('README.md')).toBe('plan');
    expect(mod.classifyRepoPath('src/index.ts')).toBe('code');
    expect(mod.classifyRepoPath('docs/maintenance/branch-cleanup-report-2026-02-28.md')).toBe('history');
    expect(mod.classifyRepoPath('tmp/maintenance/out.json')).toBe('excluded');
  });

  it('writes audit reports from batch packs and open issue fixtures', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-reference-audit-'));
    const repoDir = join(sandbox, 'repo');
    const batchDir = join(sandbox, 'batches');
    const outputDir = join(sandbox, 'out');
    const issuesPath = join(sandbox, 'open-issues.json');

    try {
      mkdirSync(repoDir, { recursive: true });
      runGit(repoDir, ['init', '-b', 'main']);
      runGit(repoDir, ['config', 'user.email', 'test@example.com']);
      runGit(repoDir, ['config', 'user.name', 'Test User']);

      mkdirSync(join(repoDir, '.github', 'workflows'), { recursive: true });
      mkdirSync(join(repoDir, 'docs'), { recursive: true });
      mkdirSync(join(repoDir, 'src'), { recursive: true });
      mkdirSync(join(repoDir, 'docs', 'maintenance'), { recursive: true });

      writeFileSync(join(repoDir, '.github', 'workflows', 'cleanup.yml'), 'branch: docs/stale-a\n', 'utf8');
      writeFileSync(join(repoDir, 'docs', 'plan.md'), 'Keep types/stale-b until plan is closed.\n', 'utf8');
      writeFileSync(join(repoDir, 'src', 'notes.ts'), 'const branch = "ci/stale-c";\n', 'utf8');
      writeFileSync(
        join(repoDir, 'docs', 'maintenance', 'branch-cleanup-report-2026-02-28.md'),
        'historical docs/stale-a\n',
        'utf8',
      );
      runGit(repoDir, ['add', '.']);
      runGit(repoDir, ['commit', '-m', 'seed']);

      mkdirSync(batchDir, { recursive: true });
      writeFileSync(
        join(batchDir, 'batch-b-low-risk-stale.json'),
        `${JSON.stringify(
          {
            generatedAt: '2026-03-08T00:00:00Z',
            batch: {
              id: 'B',
              title: 'Low-risk stale branches',
              description: 'review',
              criteria: 'sample',
            },
            sourceTriage: {
              path: '/tmp/remote-cleanup-batches/source.json',
              generatedAt: '2026-03-08T00:00:00Z',
              inventoryGeneratedAt: '2026-03-08T00:00:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            count: 3,
            items: [
              {
                branch: 'docs/stale-a',
                ageDays: 180,
                branchOid: 'oid-a',
                riskBand: 'low',
                prState: 'closed',
                prMatchMode: 'head-oid',
                latestPr: { number: 2401, state: 'closed' },
                proposedAction: 'delete-review',
                decision: '',
                notes: '',
                baseBranches: ['main'],
              },
              {
                branch: 'types/stale-b',
                ageDays: 120,
                branchOid: 'oid-b',
                riskBand: 'low',
                prState: 'merged',
                prMatchMode: 'head-oid',
                latestPr: { number: 2402, state: 'merged' },
                proposedAction: 'delete-review',
                decision: '',
                notes: '',
                baseBranches: ['main'],
              },
              {
                branch: 'ci/stale-c',
                ageDays: 150,
                branchOid: 'oid-c',
                riskBand: 'low',
                prState: 'none',
                prMatchMode: 'none',
                latestPr: null,
                proposedAction: 'delete-review',
                decision: '',
                notes: '',
                baseBranches: [],
              },
            ],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(batchDir, 'batch-c-ambiguous-stale.json'),
        `${JSON.stringify(
          {
            generatedAt: '2026-03-08T00:00:00Z',
            batch: {
              id: 'C',
              title: 'Ambiguous stale branches',
              description: 'review',
              criteria: 'sample',
            },
            sourceTriage: {
              path: '/tmp/remote-cleanup-batches/source.json',
              generatedAt: '2026-03-08T00:00:00Z',
              inventoryGeneratedAt: '2026-03-08T00:00:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            count: 1,
            items: [
              {
                branch: 'feature/ambiguous-a',
                ageDays: 200,
                branchOid: 'oid-amb',
                riskBand: 'high',
                prState: 'ambiguous',
                prMatchMode: 'branch-name-only',
                latestPr: { number: 2403, state: 'merged' },
                proposedAction: 'manual-review',
                decision: '',
                notes: '',
                baseBranches: ['main'],
              },
            ],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      writeFileSync(
        issuesPath,
        `${JSON.stringify(
          [
            {
              number: 2469,
              title: 'track types/stale-b cleanup',
              body: 'Branch types/stale-b is still referenced by the active plan.',
              html_url: 'https://example.invalid/issues/2469',
              comments_data: [
                {
                  body: 'feature/ambiguous-a still needs manual review.',
                  html_url: 'https://example.invalid/issues/2469#comment-1',
                },
              ],
            },
          ],
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync(
        'node',
        [scriptPath, '--batch-dir', batchDir, '--output-dir', outputDir, '--open-issues-json', issuesPath],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('batches=2 branches=4');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.batches['batch-b-low-risk-stale'].summary.withAutomationRefs).toBe(1);
      expect(summary.batches['batch-b-low-risk-stale'].summary.withOpenIssueRefs).toBe(1);
      expect(summary.batches['batch-b-low-risk-stale'].summary.withCodeRefs).toBe(1);
      expect(summary.batches['batch-c-ambiguous-stale'].summary.withOpenIssueRefs).toBe(1);

      const batchB = JSON.parse(readFileSync(join(outputDir, 'batch-b-low-risk-stale.audit.json'), 'utf8'));
      const docsItem = batchB.items.find((item: { branch: string }) => item.branch === 'docs/stale-a');
      const typesItem = batchB.items.find((item: { branch: string }) => item.branch === 'types/stale-b');
      const ciItem = batchB.items.find((item: { branch: string }) => item.branch === 'ci/stale-c');
      expect(docsItem.audit.reviewHint).toBe('keep-review');
      expect(docsItem.audit.repoRefSummary.automation).toBe(1);
      expect(typesItem.audit.reviewHint).toBe('keep-review');
      expect(typesItem.audit.openIssueRefs).toHaveLength(2);
      expect(ciItem.audit.reviewHint).toBe('manual-review');
      expect(ciItem.audit.repoRefSummary.code).toBe(1);

      const batchC = JSON.parse(readFileSync(join(outputDir, 'batch-c-ambiguous-stale.audit.json'), 'utf8'));
      expect(batchC.items[0].audit.reviewHint).toBe('keep-review');

      const summaryMd = readFileSync(join(outputDir, 'summary.md'), 'utf8');
      expect(summaryMd).toContain('batch-b-low-risk-stale');
      expect(summaryMd).toContain('batch-c-ambiguous-stale');

      const issueComment = readFileSync(join(outputDir, 'issue-comment.md'), 'utf8');
      expect(issueComment).toContain('Batch B: total=3');
      expect(issueComment).toContain('Batch C: total=1');

      const ignoredOutputDir = join(sandbox, 'out-ignored');
      const ignoredResult = spawnSync(
        'node',
        [
          scriptPath,
          '--batch-dir',
          batchDir,
          '--output-dir',
          ignoredOutputDir,
          '--open-issues-json',
          issuesPath,
          '--ignore-issue-number',
          '2469',
        ],
        {
          cwd: repoDir,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(ignoredResult.status, ignoredResult.stderr || ignoredResult.stdout).toBe(0);

      const ignoredSummary = JSON.parse(readFileSync(join(ignoredOutputDir, 'summary.json'), 'utf8'));
      expect(ignoredSummary.openIssues.ignoredIssueNumbers).toEqual([2469]);
      expect(ignoredSummary.batches['batch-b-low-risk-stale'].summary.withOpenIssueRefs).toBe(0);
      expect(ignoredSummary.batches['batch-c-ambiguous-stale'].summary.withOpenIssueRefs).toBe(0);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
