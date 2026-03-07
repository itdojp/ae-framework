import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/maintenance/remote-cleanup-decision-sync.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

describe.sequential('remote-cleanup-decision-sync script', () => {
  it('writes a reviewed triage manifest from reviewed batch packs', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs([])).toMatchObject({
      inputJson: 'tmp/maintenance/remote-branch-triage.json',
      batchDir: 'tmp/maintenance/remote-cleanup-batches',
      outputDir: 'tmp/maintenance/remote-cleanup-reviewed',
    });

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-decision-sync-'));
    const inputJson = join(sandbox, 'remote-branch-triage.json');
    const batchDir = join(sandbox, 'batches');
    const outputDir = join(sandbox, 'out');

    try {
      mkdirSync(batchDir, { recursive: true });
      writeFileSync(
        inputJson,
        `${JSON.stringify(
          {
            generatedAt: '2026-03-08T00:00:00Z',
            sourceInventory: {
              path: '/tmp/remote-branch-triage.json',
              generatedAt: '2026-03-08T00:00:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            remoteMerged: [],
            remoteStale: [
              {
                branch: 'docs/stale-a',
                branchOid: 'oid-a',
                ageDays: 140,
                riskBand: 'low',
                prState: 'merged',
                prMatchMode: 'head-oid',
                latestPr: { number: 2401, state: 'merged' },
                baseBranches: ['main'],
                proposedAction: 'delete-review',
                decision: '',
                notes: '',
              },
              {
                branch: 'feature/ambiguous-a',
                branchOid: 'oid-b',
                ageDays: 220,
                riskBand: 'high',
                prState: 'ambiguous',
                prMatchMode: 'branch-name-only',
                latestPr: { number: 2402, state: 'merged' },
                baseBranches: ['main'],
                proposedAction: 'manual-review',
                decision: '',
                notes: '',
              },
            ],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(batchDir, 'batch-b-low-risk-stale.json'),
        `${JSON.stringify(
          {
            generatedAt: '2026-03-08T00:10:00Z',
            sourceTriage: {
              path: inputJson,
              generatedAt: '2026-03-08T00:00:00Z',
              inventoryGeneratedAt: '2026-03-08T00:00:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            items: [
              {
                branch: 'docs/stale-a',
                branchOid: 'oid-a',
                decision: 'delete',
                notes: 'safe to remove after review',
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
            generatedAt: '2026-03-08T00:10:00Z',
            sourceTriage: {
              path: inputJson,
              generatedAt: '2026-03-08T00:00:00Z',
              inventoryGeneratedAt: '2026-03-08T00:00:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            items: [
              {
                branch: 'feature/ambiguous-a',
                branchOid: 'oid-b',
                decision: 'keep',
                notes: 'name reused historically; retain',
              },
            ],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync('node', [scriptPath, '--input-json', inputJson, '--batch-dir', batchDir, '--output-dir', outputDir], {
        cwd: repoRoot,
        encoding: 'utf8',
        timeout: 120_000,
      });

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('rows=2');

      const reviewedManifest = JSON.parse(readFileSync(join(outputDir, 'reviewed-triage.json'), 'utf8'));
      expect(reviewedManifest.remoteStale[0].decision).toBe('delete');
      expect(reviewedManifest.remoteStale[0].notes).toBe('safe to remove after review');
      expect(reviewedManifest.remoteStale[1].decision).toBe('keep');
      expect(reviewedManifest.remoteStale[1].notes).toBe('name reused historically; retain');
      expect(reviewedManifest.reviewedDecisions.sourceBatchDir).toBe(batchDir);

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.summaryByBatch.B.delete).toBe(1);
      expect(summary.summaryByBatch.C.keep).toBe(1);
      expect(summary.appliedRows).toHaveLength(2);

      const summaryMd = readFileSync(join(outputDir, 'summary.md'), 'utf8');
      expect(summaryMd).toContain('Remote Cleanup Decision Sync');
      expect(summaryMd).toContain('Low-risk stale branches');

      const issueComment = readFileSync(join(outputDir, 'issue-comment.md'), 'utf8');
      expect(issueComment).toContain('no remote delete was executed');
      expect(issueComment).toContain('reviewed-triage.json');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects reviewed batch rows when branchOid mismatches the source triage row', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-decision-sync-'));
    const inputJson = join(sandbox, 'remote-branch-triage.json');
    const batchDir = join(sandbox, 'batches');
    const outputDir = join(sandbox, 'out');

    try {
      mkdirSync(batchDir, { recursive: true });
      writeFileSync(
        inputJson,
        `${JSON.stringify(
          {
            sourceInventory: { base: 'origin/main', remote: 'origin' },
            remoteMerged: [],
            remoteStale: [{ branch: 'docs/stale-a', branchOid: 'oid-a', decision: '', notes: '' }],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(batchDir, 'batch-b-low-risk-stale.json'),
        `${JSON.stringify(
          {
            generatedAt: '2026-03-08T00:10:00Z',
            sourceTriage: {
              path: inputJson,
              generatedAt: '',
              inventoryGeneratedAt: '',
              base: 'origin/main',
              remote: 'origin',
            },
            items: [{ branch: 'docs/stale-a', branchOid: 'oid-b', decision: 'delete', notes: '' }],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync('node', [scriptPath, '--input-json', inputJson, '--batch-dir', batchDir, '--output-dir', outputDir], {
        cwd: repoRoot,
        encoding: 'utf8',
        timeout: 120_000,
      });

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('branchOid mismatch');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects delete sync when PR lookup coverage is truncated and prState is none', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-decision-sync-'));
    const inputJson = join(sandbox, 'remote-branch-triage.json');
    const batchDir = join(sandbox, 'batches');
    const outputDir = join(sandbox, 'out');

    try {
      mkdirSync(batchDir, { recursive: true });
      writeFileSync(
        inputJson,
        `${JSON.stringify(
          {
            generatedAt: '2026-03-08T00:00:00Z',
            sourceInventory: {
              path: inputJson,
              generatedAt: '2026-03-08T00:00:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            githubPullRequests: {
              lookupCoverage: 'truncated',
            },
            remoteMerged: [],
            remoteStale: [
              {
                branch: 'docs/stale-a',
                branchOid: 'oid-a',
                prState: 'none',
                decision: '',
                notes: '',
              },
            ],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(batchDir, 'batch-b-low-risk-stale.json'),
        `${JSON.stringify(
          {
            generatedAt: '2026-03-08T00:10:00Z',
            sourceTriage: {
              path: inputJson,
              generatedAt: '2026-03-08T00:00:00Z',
              inventoryGeneratedAt: '2026-03-08T00:00:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            items: [{ branch: 'docs/stale-a', branchOid: 'oid-a', decision: 'delete', notes: '' }],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync('node', [scriptPath, '--input-json', inputJson, '--batch-dir', batchDir, '--output-dir', outputDir], {
        cwd: repoRoot,
        encoding: 'utf8',
        timeout: 120_000,
      });

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('lookup coverage is truncated');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects duplicate reviewed branch rows in batch input', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-decision-sync-'));
    const inputJson = join(sandbox, 'remote-branch-triage.json');
    const batchDir = join(sandbox, 'batches');
    const outputDir = join(sandbox, 'out');

    try {
      mkdirSync(batchDir, { recursive: true });
      writeFileSync(
        inputJson,
        `${JSON.stringify(
          {
            generatedAt: '2026-03-08T00:00:00Z',
            sourceInventory: {
              path: inputJson,
              generatedAt: '2026-03-08T00:00:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            remoteMerged: [],
            remoteStale: [{ branch: 'docs/stale-a', branchOid: 'oid-a', prState: 'merged', decision: '', notes: '' }],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(batchDir, 'batch-b-low-risk-stale.json'),
        `${JSON.stringify(
          {
            generatedAt: '2026-03-08T00:10:00Z',
            sourceTriage: {
              path: inputJson,
              generatedAt: '2026-03-08T00:00:00Z',
              inventoryGeneratedAt: '2026-03-08T00:00:00Z',
              base: 'origin/main',
              remote: 'origin',
            },
            items: [
              { branch: 'docs/stale-a', branchOid: 'oid-a', decision: 'keep', notes: '' },
              { branch: 'docs/stale-a', branchOid: 'oid-a', decision: 'delete', notes: '' },
            ],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync('node', [scriptPath, '--input-json', inputJson, '--batch-dir', batchDir, '--output-dir', outputDir], {
        cwd: repoRoot,
        encoding: 'utf8',
        timeout: 120_000,
      });

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('duplicate reviewed branch row');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
