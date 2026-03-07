import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/maintenance/remote-cleanup-batches.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

describe.sequential('remote-cleanup-batches script', () => {
  it('selects batch A/B/C review sets from triage data', async () => {
    const mod = await import(moduleUrl);

    const batches = mod.selectReviewBatches(
      {
        generatedAt: '2026-03-07T08:00:00Z',
        sourceInventory: {
          path: 'tmp/maintenance/remote-branch-triage.json',
          generatedAt: '2026-03-07T07:55:00Z',
          base: 'origin/main',
          remote: 'origin',
        },
        summary: {
          remoteMergedCandidates: 1,
          remoteStaleCandidates: 4,
        },
        remoteMerged: [
          {
            branch: 'docs/merged-a',
            branchOid: 'oid-merged-a',
            prState: 'merged',
            prMatchMode: 'head-oid',
            latestPr: { number: 2401, state: 'merged' },
            baseBranches: ['main'],
            approval: 'required',
            deleteCommand: 'git push origin --delete docs/merged-a',
          },
        ],
        remoteStale: [
          {
            branch: 'docs/stale-a',
            ageDays: 180,
            branchOid: 'oid-stale-a',
            riskBand: 'low',
            prState: 'closed',
            prMatchMode: 'head-oid',
            latestPr: { number: 2402, state: 'closed' },
            proposedAction: 'delete-review',
            decision: '',
            notes: '',
            baseBranches: ['main'],
          },
          {
            branch: 'types/stale-b',
            ageDays: 140,
            branchOid: 'oid-stale-b',
            riskBand: 'low',
            prState: 'merged',
            prMatchMode: 'head-oid',
            latestPr: { number: 2403, state: 'merged' },
            proposedAction: 'delete-review',
            decision: '',
            notes: '',
            baseBranches: ['main'],
          },
          {
            branch: 'feature/ambiguous-a',
            ageDays: 200,
            branchOid: 'oid-ambiguous-a',
            riskBand: 'high',
            prState: 'ambiguous',
            prMatchMode: 'branch-name-only',
            latestPr: { number: 2404, state: 'merged' },
            proposedAction: 'manual-review',
            decision: '',
            notes: '',
            baseBranches: ['main'],
          },
          {
            branch: 'docs/ambiguous-b',
            ageDays: 220,
            branchOid: 'oid-ambiguous-b',
            riskBand: 'low',
            prState: 'ambiguous',
            prMatchMode: 'branch-name-only',
            latestPr: { number: 2405, state: 'merged' },
            proposedAction: 'manual-review',
            decision: '',
            notes: '',
            baseBranches: ['main'],
          },
        ],
      },
      { outputDir: '/tmp/remote-cleanup-batches', sourceTriagePath: '/tmp/remote-branch-triage.json' },
    );

    expect(batches.batchA.payload.count).toBe(1);
    expect(batches.batchA.payload.items).toEqual([
      expect.objectContaining({ branch: 'docs/merged-a', deleteCommand: 'git push origin --delete docs/merged-a' }),
    ]);
    expect(batches.batchA.payload.sourceTriage.path).toBe('/tmp/remote-branch-triage.json');

    expect(batches.batchB.payload.items.map((item: { branch: string }) => item.branch)).toEqual([
      'docs/stale-a',
      'types/stale-b',
    ]);
    expect(batches.batchC.payload.items.map((item: { branch: string }) => item.branch)).toEqual([
      'feature/ambiguous-a',
      'docs/ambiguous-b',
    ]);
  });

  it('writes summary, markdown, branch lists, and issue comment files', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-batches-'));
    const inputPath = join(sandbox, 'remote-branch-triage.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeFileSync(
        inputPath,
        `${JSON.stringify(
          {
            generatedAt: '2026-03-07T08:00:00Z',
            sourceInventory: {
              path: 'tmp/maintenance/remote-branch-triage.json',
              generatedAt: '2026-03-07T07:55:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            summary: {
              remoteMergedCandidates: 0,
              remoteStaleCandidates: 2,
              staleByRiskBand: { low: 1, standard: 0, high: 1 },
              staleByPrState: { open: 0, closed: 1, merged: 0, none: 0, ambiguous: 1, unavailable: 0 },
            },
            remoteMerged: [],
            remoteStale: [
              {
                branch: 'docs/stale-a',
                ageDays: 180,
                branchOid: 'oid-stale-a',
                riskBand: 'low',
                prState: 'closed',
                prMatchMode: 'head-oid',
                latestPr: { number: 2402, state: 'closed' },
                proposedAction: 'delete-review',
                decision: '',
                notes: 'review needed',
                baseBranches: ['main'],
              },
              {
                branch: 'feature/ambiguous-a',
                ageDays: 200,
                branchOid: 'oid-ambiguous-a',
                riskBand: 'high',
                prState: 'ambiguous',
                prMatchMode: 'branch-name-only',
                latestPr: { number: 2404, state: 'merged' },
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

      const result = spawnSync('node', [scriptPath, '--input-json', inputPath, '--output-dir', outputDir], {
        cwd: repoRoot,
        encoding: 'utf8',
        timeout: 120_000,
      });

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('batchA=0 batchB=1 batchC=1');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.batches.batchA.count).toBe(0);
      expect(summary.batches.batchB.count).toBe(1);
      expect(summary.batches.batchC.count).toBe(1);
      expect(summary.batches.batchB.csvPath).toContain('batch-b-low-risk-stale.csv');
      expect(summary.batches.batchC.csvPath).toContain('batch-c-ambiguous-stale.csv');

      const summaryMd = readFileSync(join(outputDir, 'summary.md'), 'utf8');
      expect(summaryMd).toContain('Batch A (merged): 0');
      expect(summaryMd).toContain('Batch B (low-risk stale): 1');
      expect(summaryMd).toContain('Batch C (ambiguous stale): 1');
      expect(summaryMd).toContain(`source triage: \`${inputPath}\``);

      const batchBMd = readFileSync(join(outputDir, 'batch-b-low-risk-stale.md'), 'utf8');
      expect(batchBMd).toContain('docs/stale-a');
      expect(batchBMd).not.toContain('feature/ambiguous-a');

      const batchCMd = readFileSync(join(outputDir, 'batch-c-ambiguous-stale.md'), 'utf8');
      expect(batchCMd).toContain('feature/ambiguous-a');

      const batchBBranches = readFileSync(join(outputDir, 'batch-b-low-risk-stale.branches.txt'), 'utf8');
      expect(batchBBranches.trim()).toBe('docs/stale-a');

      const batchACommands = readFileSync(join(outputDir, 'batch-a-merged.commands.sh'), 'utf8');
      expect(batchACommands).toBe('');

      const batchBCsv = readFileSync(join(outputDir, 'batch-b-low-risk-stale.csv'), 'utf8');
      expect(batchBCsv).toContain('branch,ageDays,branchOid,riskBand,prState,prMatchMode,latestPr,baseBranches,proposedAction,decision,notes');
      expect(batchBCsv).toContain('docs/stale-a,180,oid-stale-a,low,closed,head-oid,#2402 (closed),main,delete-review,,review needed');

      const issueComment = readFileSync(join(outputDir, 'issue-comment.md'), 'utf8');
      expect(issueComment).toContain('Batch B (low-risk stale): 1');
      expect(issueComment).toContain('Batch C (ambiguous stale): 1');
      expect(issueComment).toContain('batch-b-low-risk-stale.csv');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
