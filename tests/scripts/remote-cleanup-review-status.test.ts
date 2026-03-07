import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/maintenance/remote-cleanup-review-status.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

describe.sequential('remote-cleanup-review-status script', () => {
  it('classifies reviewed rows into ready, blocked, retained, pending, and missing-audit', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs([])).toMatchObject({
      reviewedManifestJson: 'tmp/maintenance/remote-cleanup-reviewed/reviewed-triage.json',
      referenceAuditDir: 'tmp/maintenance/remote-cleanup-reference-audit',
      outputDir: 'tmp/maintenance/remote-cleanup-review-status',
    });

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-review-status-'));
    const reviewedManifestPath = join(sandbox, 'reviewed-triage.json');
    const auditDir = join(sandbox, 'audit');
    const outputDir = join(sandbox, 'out');

    try {
      mkdirSync(auditDir, { recursive: true });

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
            },
            remoteStale: [
              { branch: 'docs/stale-a', branchOid: 'oid-a', prState: 'merged', decision: 'delete', notes: 'ready' },
              { branch: 'docs/stale-b', branchOid: 'oid-b', prState: 'closed', decision: 'delete', notes: 'blocked by refs' },
              { branch: 'docs/stale-c', branchOid: 'oid-c', prState: 'none', decision: 'keep', notes: 'retain' },
              { branch: 'feature/ambiguous-a', branchOid: 'oid-d', prState: 'ambiguous', decision: '', notes: '' },
              { branch: 'docs/missing-audit', branchOid: 'oid-e', prState: 'merged', decision: 'delete', notes: 'missing' },
            ],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      writeFileSync(
        join(auditDir, 'batch-b-low-risk-stale.audit.json'),
        `${JSON.stringify(
          {
            batch: { id: 'B', title: 'Low-risk stale branches' },
            sourceTriage: {
              path: '/tmp/remote-branch-triage.json',
              base: 'origin/main',
              remote: 'origin',
            },
            summary: { total: 3, clearCandidates: 1 },
            items: [
              {
                branch: 'docs/stale-a',
                branchOid: 'oid-a',
                audit: {
                  reviewHint: 'delete-candidate',
                  openIssueRefs: [],
                  repoRefs: [],
                  repoRefSummary: { automation: 0, plan: 0, code: 0, history: 0 },
                },
              },
              {
                branch: 'docs/stale-b',
                branchOid: 'oid-b',
                audit: {
                  reviewHint: 'manual-review',
                  openIssueRefs: [],
                  repoRefs: [],
                  repoRefSummary: { automation: 0, plan: 1, code: 0, history: 0 },
                },
              },
              {
                branch: 'docs/stale-c',
                branchOid: 'oid-c',
                audit: {
                  reviewHint: 'keep-review',
                  openIssueRefs: [{ number: 2001 }],
                  repoRefs: [],
                  repoRefSummary: { automation: 0, plan: 0, code: 0, history: 0 },
                },
              },
            ],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      writeFileSync(
        join(auditDir, 'batch-c-ambiguous-stale.audit.json'),
        `${JSON.stringify(
          {
            batch: { id: 'C', title: 'Ambiguous stale branches' },
            sourceTriage: {
              path: '/tmp/remote-branch-triage.json',
              base: 'origin/main',
              remote: 'origin',
            },
            summary: { total: 1, clearCandidates: 1 },
            items: [
              {
                branch: 'feature/ambiguous-a',
                branchOid: 'oid-d',
                audit: {
                  reviewHint: 'manual-review',
                  openIssueRefs: [],
                  repoRefs: [],
                  repoRefSummary: { automation: 0, plan: 0, code: 0, history: 0 },
                },
              },
            ],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync(
        'node',
        [scriptPath, '--reviewed-manifest-json', reviewedManifestPath, '--reference-audit-dir', auditDir, '--output-dir', outputDir],
        {
          cwd: repoRoot,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('ready=1 blocked=1 pending=1');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.overall['delete-ready']).toBe(1);
      expect(summary.overall['delete-blocked']).toBe(1);
      expect(summary.overall.retained).toBe(1);
      expect(summary.overall['pending-review']).toBe(1);
      expect(summary.overall['missing-audit']).toBe(1);
      expect(summary.batches.B['delete-ready']).toBe(1);
      expect(summary.batches.C['pending-review']).toBe(1);

      const deleteReady = JSON.parse(readFileSync(join(outputDir, 'delete-ready.json'), 'utf8'));
      expect(deleteReady).toHaveLength(1);
      expect(deleteReady[0].branch).toBe('docs/stale-a');

      const deleteReadyBranchList = JSON.parse(readFileSync(join(outputDir, 'delete-ready.branches.json'), 'utf8'));
      expect(deleteReadyBranchList.branches).toEqual([
        { branch: 'docs/stale-a', branchOid: 'oid-a', decision: 'delete', prState: 'merged' },
      ]);

      const blocked = JSON.parse(readFileSync(join(outputDir, 'delete-blocked.json'), 'utf8'));
      expect(blocked[0].branch).toBe('docs/stale-b');

      const retained = JSON.parse(readFileSync(join(outputDir, 'retained.json'), 'utf8'));
      expect(retained[0].branch).toBe('docs/stale-c');

      const pending = JSON.parse(readFileSync(join(outputDir, 'pending-review.json'), 'utf8'));
      expect(pending[0].branch).toBe('feature/ambiguous-a');

      const missing = JSON.parse(readFileSync(join(outputDir, 'missing-audit.json'), 'utf8'));
      expect(missing[0].branch).toBe('docs/missing-audit');

      const issueComment = readFileSync(join(outputDir, 'issue-comment.md'), 'utf8');
      expect(issueComment).toContain('delete-ready: 1');
      expect(issueComment).toContain('delete-ready.branches.json');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects reference audits that do not match the reviewed manifest source triage', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-review-status-'));
    const reviewedManifestPath = join(sandbox, 'reviewed-triage.json');
    const auditDir = join(sandbox, 'audit');
    const outputDir = join(sandbox, 'out');

    try {
      mkdirSync(auditDir, { recursive: true });
      writeFileSync(
        reviewedManifestPath,
        `${JSON.stringify(
          {
            sourceInventory: {
              base: 'origin/main',
              remote: 'origin',
            },
            reviewedDecisions: {
              sourceTriagePath: '/tmp/expected-triage.json',
            },
            remoteStale: [],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );
      writeFileSync(
        join(auditDir, 'batch-b-low-risk-stale.audit.json'),
        `${JSON.stringify(
          {
            batch: { id: 'B', title: 'Low-risk stale branches' },
            sourceTriage: {
              path: '/tmp/other-triage.json',
              base: 'origin/main',
              remote: 'origin',
            },
            items: [],
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync(
        'node',
        [scriptPath, '--reviewed-manifest-json', reviewedManifestPath, '--reference-audit-dir', auditDir, '--output-dir', outputDir],
        {
          cwd: repoRoot,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('does not match reviewed manifest source triage');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
