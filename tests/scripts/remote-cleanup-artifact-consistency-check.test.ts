import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/maintenance/remote-cleanup-artifact-consistency-check.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

const writeJson = (targetPath: string, value: unknown) => {
  mkdirSync(dirname(targetPath), { recursive: true });
  writeFileSync(targetPath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
};

const createFixture = (sandbox: string, options: { includePostApply?: boolean; includeRefreshAudit?: boolean } = {}) => {
  const triagePath = join(sandbox, 'remote-branch-triage.json');
  const batchDir = join(sandbox, 'batches');
  const auditDir = join(sandbox, 'reference-audit');
  const reviewedDir = join(sandbox, 'reviewed');
  const reviewStatusDir = join(sandbox, 'review-status');
  const executionPackDir = join(sandbox, 'execution-pack');
  const postVerifyDir = join(sandbox, 'post-verify');
  const refreshAuditDir = join(sandbox, 'refresh-audit');

  mkdirSync(batchDir, { recursive: true });
  mkdirSync(auditDir, { recursive: true });
  mkdirSync(reviewedDir, { recursive: true });
  mkdirSync(reviewStatusDir, { recursive: true });
  mkdirSync(executionPackDir, { recursive: true });
  mkdirSync(postVerifyDir, { recursive: true });
  mkdirSync(refreshAuditDir, { recursive: true });

  const triageGeneratedAt = '2026-03-08T00:00:00Z';
  const inventoryGeneratedAt = '2026-03-08T00:00:00Z';
  const base = 'origin/main';
  const remote = 'origin';

  writeJson(triagePath, {
    generatedAt: triageGeneratedAt,
    sourceInventory: {
      path: triagePath,
      generatedAt: inventoryGeneratedAt,
      base,
      remote,
    },
    summary: {
      remoteMergedCandidates: 1,
      remoteStaleCandidates: 2,
    },
    remoteMerged: [
      {
        branch: 'docs/merged-a',
        branchOid: 'oid-merged-a',
        prState: 'merged',
        prMatchMode: 'head-oid',
        latestPr: { number: 10 },
        baseBranches: ['main'],
        approval: 'required',
        deleteCommand: 'git push origin --delete docs/merged-a',
      },
    ],
    remoteStale: [
      {
        branch: 'docs/stale-a',
        ageDays: 14,
        branchOid: 'oid-stale-a',
        riskBand: 'low',
        prState: 'closed',
        prMatchMode: 'branch-name-only',
        latestPr: null,
        proposedAction: 'delete',
        decision: 'delete',
        notes: 'remove',
        baseBranches: ['main'],
      },
      {
        branch: 'ci/ambiguous-a',
        ageDays: 32,
        branchOid: 'oid-ambiguous-a',
        riskBand: 'standard',
        prState: 'ambiguous',
        prMatchMode: 'branch-name-only',
        latestPr: null,
        proposedAction: 'keep',
        decision: 'keep',
        notes: 'reuse risk',
        baseBranches: ['main'],
      },
    ],
  });

  const batchPaths = {
    batchA: join(batchDir, 'batch-a-merged.json'),
    batchB: join(batchDir, 'batch-b-low-risk-stale.json'),
    batchC: join(batchDir, 'batch-c-ambiguous-stale.json'),
  };
  const sourceTriage = {
    path: triagePath,
    generatedAt: triageGeneratedAt,
    inventoryGeneratedAt,
    base,
    remote,
  };
  writeJson(batchPaths.batchA, {
    generatedAt: '2026-03-08T00:05:00Z',
    count: 1,
    sourceTriage,
    batch: { id: 'A', title: 'Merged remote branches' },
    items: [{ branch: 'docs/merged-a', branchOid: 'oid-merged-a', prState: 'merged', prMatchMode: 'head-oid', latestPr: { number: 10 }, baseBranches: ['main'], approval: 'required', deleteCommand: 'git push origin --delete docs/merged-a' }],
  });
  writeJson(batchPaths.batchB, {
    generatedAt: '2026-03-08T00:05:00Z',
    count: 1,
    sourceTriage,
    batch: { id: 'B', title: 'Low-risk stale branches' },
    items: [{ branch: 'docs/stale-a', ageDays: 14, branchOid: 'oid-stale-a', riskBand: 'low', prState: 'closed', prMatchMode: 'branch-name-only', latestPr: null, proposedAction: 'delete', decision: 'delete', notes: 'remove', baseBranches: ['main'] }],
  });
  writeJson(batchPaths.batchC, {
    generatedAt: '2026-03-08T00:05:00Z',
    count: 1,
    sourceTriage,
    batch: { id: 'C', title: 'Ambiguous stale branches' },
    items: [{ branch: 'ci/ambiguous-a', ageDays: 32, branchOid: 'oid-ambiguous-a', riskBand: 'standard', prState: 'ambiguous', prMatchMode: 'branch-name-only', latestPr: null, proposedAction: 'keep', decision: 'keep', notes: 'reuse risk', baseBranches: ['main'] }],
  });
  writeJson(join(batchDir, 'summary.json'), {
    generatedAt: '2026-03-08T00:05:30Z',
    sourceTriage: {
      path: triagePath,
      generatedAt: triageGeneratedAt,
      base,
      remote,
    },
    batches: {
      batchA: { id: 'A', count: 1, jsonPath: batchPaths.batchA },
      batchB: { id: 'B', count: 1, jsonPath: batchPaths.batchB },
      batchC: { id: 'C', count: 1, jsonPath: batchPaths.batchC },
    },
  });

  const auditPayload = (id: 'A' | 'B' | 'C', slug: string, branch: string) => ({
    generatedAt: '2026-03-08T00:06:00Z',
    batch: { id, title: slug },
    sourceTriage,
    items: [{ branch, batchId: id }],
    summary: {
      total: 1,
      withOpenIssueRefs: 0,
      withAutomationRefs: 0,
      withPlanRefs: 0,
      withCodeRefs: 0,
      clearCandidates: 1,
    },
  });
  const auditPaths = {
    a: join(auditDir, 'batch-a-merged.audit.json'),
    b: join(auditDir, 'batch-b-low-risk-stale.audit.json'),
    c: join(auditDir, 'batch-c-ambiguous-stale.audit.json'),
  };
  writeJson(auditPaths.a, auditPayload('A', 'Merged', 'docs/merged-a'));
  writeJson(auditPaths.b, auditPayload('B', 'Low risk', 'docs/stale-a'));
  writeJson(auditPaths.c, auditPayload('C', 'Ambiguous', 'ci/ambiguous-a'));
  writeJson(join(auditDir, 'summary.json'), {
    generatedAt: '2026-03-08T00:06:30Z',
    source: { batchDir },
    batches: {
      'batch-a-merged': { id: 'A', summary: { total: 1, clearCandidates: 1 }, jsonPath: auditPaths.a },
      'batch-b-low-risk-stale': { id: 'B', summary: { total: 1, clearCandidates: 1 }, jsonPath: auditPaths.b },
      'batch-c-ambiguous-stale': { id: 'C', summary: { total: 1, clearCandidates: 1 }, jsonPath: auditPaths.c },
    },
  });

  const reviewedManifestPath = join(reviewedDir, 'reviewed-triage.json');
  const reviewedSummaryPath = join(reviewedDir, 'summary.json');
  const reviewedDecisions = {
    generatedAt: '2026-03-08T00:07:00Z',
    sourceTriagePath: triagePath,
    sourceBatchDir: batchDir,
    sourceBatches: ['batch-b-low-risk-stale.json', 'batch-c-ambiguous-stale.json'],
    reviewInputFormat: 'json',
    summaryByBatch: {
      B: { id: 'B', title: 'Low-risk stale branches', total: 1, keep: 0, archive: 0, delete: 1, pending: 0, updated: 1, unchanged: 0 },
      C: { id: 'C', title: 'Ambiguous stale branches', total: 1, keep: 1, archive: 0, delete: 0, pending: 0, updated: 1, unchanged: 0 },
    },
  };
  writeJson(reviewedManifestPath, {
    sourceInventory: {
      path: triagePath,
      generatedAt: inventoryGeneratedAt,
      base,
      remote,
    },
    reviewedDecisions,
    remoteStale: [
      { branch: 'docs/stale-a', branchOid: 'oid-stale-a', decision: 'delete', notes: 'remove', prState: 'closed', riskBand: 'low' },
      { branch: 'ci/ambiguous-a', branchOid: 'oid-ambiguous-a', decision: 'keep', notes: 'reuse risk', prState: 'ambiguous', riskBand: 'standard' },
    ],
  });
  writeJson(reviewedSummaryPath, {
    generatedAt: reviewedDecisions.generatedAt,
    sourceTriagePath: triagePath,
    sourceBatchDir: batchDir,
    sourceBatches: reviewedDecisions.sourceBatches,
    reviewInputFormat: 'json',
    reviewedManifestPath,
    summaryByBatch: reviewedDecisions.summaryByBatch,
    appliedRows: [
      { batchId: 'B', branch: 'docs/stale-a', decision: 'delete' },
      { batchId: 'C', branch: 'ci/ambiguous-a', decision: 'keep' },
    ],
  });

  const deleteReady = [{ branch: 'docs/stale-a', branchOid: 'oid-stale-a', status: 'delete-ready', decision: 'delete', batchId: 'B' }];
  writeJson(join(reviewStatusDir, 'summary.json'), {
    generatedAt: '2026-03-08T00:08:00Z',
    source: {
      reviewedManifestPath,
      referenceAuditDir: auditDir,
      sourceTriagePath: triagePath,
    },
    mergedAudit: { total: 1, clearCandidates: 1 },
    overall: {
      'delete-ready': 1,
      'delete-blocked': 0,
      retained: 1,
      'pending-review': 0,
      'missing-audit': 0,
    },
    batches: {
      B: { total: 1, 'delete-ready': 1, 'delete-blocked': 0, retained: 0, 'pending-review': 0, 'missing-audit': 0 },
      C: { total: 1, 'delete-ready': 0, 'delete-blocked': 0, retained: 1, 'pending-review': 0, 'missing-audit': 0 },
    },
  });
  writeJson(join(reviewStatusDir, 'delete-ready.json'), deleteReady);
  writeJson(join(reviewStatusDir, 'delete-ready.branches.json'), { branches: [{ branch: 'docs/stale-a', branchOid: 'oid-stale-a', decision: 'delete' }] });
  writeJson(join(reviewStatusDir, 'delete-blocked.json'), []);
  writeJson(join(reviewStatusDir, 'pending-review.json'), []);
  writeJson(join(reviewStatusDir, 'retained.json'), [{ branch: 'ci/ambiguous-a', status: 'retained', decision: 'keep', batchId: 'C' }]);
  writeJson(join(reviewStatusDir, 'missing-audit.json'), []);

  const approvedBranchesPath = join(executionPackDir, 'approved-remote-branches.json');
  const dryRunReportPath = join(executionPackDir, 'branch-cleanup-dry-run-report.json');
  const applyReportPath = join(executionPackDir, 'branch-cleanup-apply-report.json');
  writeJson(approvedBranchesPath, {
    generatedAt: '2026-03-08T00:09:00Z',
    sourceReviewStatus: {
      dir: reviewStatusDir,
      summaryPath: join(reviewStatusDir, 'summary.json'),
      deleteReadyPath: join(reviewStatusDir, 'delete-ready.json'),
      deleteReadyBranchesPath: join(reviewStatusDir, 'delete-ready.branches.json'),
      generatedAt: '2026-03-08T00:08:00Z',
      reviewedManifestPath,
      referenceAuditDir: auditDir,
      sourceTriagePath: triagePath,
    },
    sourceInventory: {
      path: triagePath,
      generatedAt: inventoryGeneratedAt,
      base,
      remote,
    },
    branches: [{ branch: 'docs/stale-a', branchOid: 'oid-stale-a', decision: 'delete' }],
  });
  writeJson(dryRunReportPath, {
    remote: {
      selection: {
        mode: 'branch-list',
        sourcePath: approvedBranchesPath,
        expectedBase: base,
        expectedRemote: remote,
      },
      totalCandidates: 1,
      plannedDetailed: [{ branch: 'docs/stale-a', branchOid: 'oid-stale-a', actualOid: 'oid-stale-a' }],
      blocked: [],
    },
  });
  writeJson(join(executionPackDir, 'summary.json'), {
    generatedAt: '2026-03-08T00:09:30Z',
    source: {
      reviewStatusDir,
      reviewedManifestPath,
      sourceTriagePath: triagePath,
      referenceAuditDir: auditDir,
    },
    sourceInventory: {
      path: triagePath,
      generatedAt: inventoryGeneratedAt,
      base,
      remote,
    },
    deleteReady: { count: 1 },
    dryRun: { planned: 1, blocked: 0 },
    artifacts: {
      approvedBranchListPath: approvedBranchesPath,
      dryRunReportPath,
      commandsPath: join(executionPackDir, 'commands.sh'),
      applyCommandPath: join(executionPackDir, 'apply-command.txt'),
    },
  });
  writeFileSync(join(executionPackDir, 'commands.sh'), '#!/usr/bin/env bash\n', 'utf8');
  writeFileSync(join(executionPackDir, 'apply-command.txt'), 'node branch-cleanup.mjs --apply\n', 'utf8');

  const paths = {
    triagePath,
    batchDir,
    auditDir,
    reviewedDir,
    reviewStatusDir,
    executionPackDir,
    postVerifySummaryPath: join(postVerifyDir, 'summary.json'),
    refreshAuditSummaryPath: join(refreshAuditDir, 'summary.json'),
    refreshedTriagePath: join(sandbox, 'refreshed-remote-branch-triage.json'),
    applyReportPath,
  };

  if (options.includePostApply) {
    writeJson(applyReportPath, {
      remoteName: remote,
      scope: 'remote',
      remote: {
        selection: {
          mode: 'branch-list',
          sourcePath: approvedBranchesPath,
          expectedBase: base,
          expectedRemote: remote,
        },
        plannedDetailed: [{ branch: 'docs/stale-a', branchOid: 'oid-stale-a', actualOid: 'oid-stale-a' }],
        deleted: ['docs/stale-a'],
        failed: [],
        blocked: [],
      },
    });
    writeJson(paths.postVerifySummaryPath, {
      generatedAt: '2026-03-08T00:10:00Z',
      source: { cleanupReportPath: applyReportPath },
      remoteName: remote,
      scope: 'remote',
      deleted: [{ branch: 'docs/stale-a', status: 'verified-absent', actualOid: '' }],
      failedDeletes: [],
      blocked: [],
      plannedButNotDeleted: [],
      counts: {
        reportedDeleted: 1,
        verifiedAbsent: 1,
        stillPresent: 0,
        failedDeletes: 0,
        blocked: 0,
        plannedButNotDeleted: 0,
      },
    });
  }

  if (options.includeRefreshAudit) {
    writeJson(paths.refreshedTriagePath, {
      generatedAt: '2026-03-08T00:11:00Z',
      sourceInventory: {
        path: paths.refreshedTriagePath,
        generatedAt: '2026-03-08T00:11:00Z',
        base,
        remote,
      },
      remoteMerged: [{ branch: 'docs/merged-a' }],
      remoteStale: [{ branch: 'docs/other-stale' }],
    });
    writeJson(paths.refreshAuditSummaryPath, {
      generatedAt: '2026-03-08T00:11:30Z',
      source: {
        postVerifySummaryPath: paths.postVerifySummaryPath,
        refreshedTriagePath: paths.refreshedTriagePath,
      },
      audit: [{ branch: 'docs/stale-a', status: 'confirmed-removed', refreshedLocations: [] }],
      counts: {
        verifiedAbsentInput: 1,
        confirmedRemoved: 1,
        reappearedInTriage: 0,
        refreshedRemoteMerged: 1,
        refreshedRemoteStale: 1,
      },
    });
  }

  return paths;
};

describe.sequential('remote-cleanup-artifact-consistency-check script', () => {
  it('validates the pre-apply artifact chain', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs([])).toMatchObject({
      triageJson: 'tmp/maintenance/remote-branch-triage.json',
      batchDir: 'tmp/maintenance/remote-cleanup-batches',
      executionPackDir: 'tmp/maintenance/remote-cleanup-execution-pack',
      outputDir: 'tmp/maintenance/remote-cleanup-artifact-consistency',
    });

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-artifact-consistency-'));
    const outputDir = join(sandbox, 'out');

    try {
      const fixture = createFixture(sandbox);
      const result = spawnSync(
        'node',
        [
          scriptPath,
          '--triage-json', fixture.triagePath,
          '--batch-dir', fixture.batchDir,
          '--reference-audit-dir', fixture.auditDir,
          '--reviewed-dir', fixture.reviewedDir,
          '--review-status-dir', fixture.reviewStatusDir,
          '--execution-pack-dir', fixture.executionPackDir,
          '--post-verify-summary-json', fixture.postVerifySummaryPath,
          '--refresh-audit-summary-json', fixture.refreshAuditSummaryPath,
          '--output-dir', outputDir,
        ],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('postApply=no refresh=no');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.counts.triage).toEqual({ remoteMerged: 1, remoteStale: 2 });
      expect(summary.counts.batches).toEqual({ A: 1, B: 1, C: 1 });
      expect(summary.counts.executionPack).toEqual({ approvedBranches: 1, dryRunPlanned: 1, dryRunBlocked: 0 });
      expect(summary.optional.postApplyVerify.available).toBe(false);
      expect(summary.optional.refreshAudit.available).toBe(false);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('validates optional post-apply and refresh-audit artifacts when present', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-artifact-consistency-post-'));
    const outputDir = join(sandbox, 'out');

    try {
      const fixture = createFixture(sandbox, { includePostApply: true, includeRefreshAudit: true });
      const result = spawnSync(
        'node',
        [
          scriptPath,
          '--triage-json', fixture.triagePath,
          '--batch-dir', fixture.batchDir,
          '--reference-audit-dir', fixture.auditDir,
          '--reviewed-dir', fixture.reviewedDir,
          '--review-status-dir', fixture.reviewStatusDir,
          '--execution-pack-dir', fixture.executionPackDir,
          '--post-verify-summary-json', fixture.postVerifySummaryPath,
          '--refresh-audit-summary-json', fixture.refreshAuditSummaryPath,
          '--output-dir', outputDir,
        ],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('postApply=yes refresh=yes');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.optional.postApplyVerify.counts).toMatchObject({ reportedDeleted: 1, verifiedAbsent: 1, stillPresent: 0 });
      expect(summary.optional.refreshAudit.counts).toMatchObject({ verifiedAbsentInput: 1, confirmedRemoved: 1, reappearedInTriage: 0 });
      const issueComment = readFileSync(join(outputDir, 'issue-comment.md'), 'utf8');
      expect(issueComment).toContain('post-apply verify: validated');
      expect(issueComment).toContain('refresh-audit: validated');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('fails on path drift between triage and batch summary', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-artifact-consistency-path-'));
    const outputDir = join(sandbox, 'out');

    try {
      const fixture = createFixture(sandbox);
      const batchSummaryPath = join(fixture.batchDir, 'summary.json');
      const batchSummary = JSON.parse(readFileSync(batchSummaryPath, 'utf8'));
      batchSummary.sourceTriage.path = join(sandbox, 'different-triage.json');
      writeJson(batchSummaryPath, batchSummary);

      const result = spawnSync(
        'node',
        [
          scriptPath,
          '--triage-json', fixture.triagePath,
          '--batch-dir', fixture.batchDir,
          '--reference-audit-dir', fixture.auditDir,
          '--reviewed-dir', fixture.reviewedDir,
          '--review-status-dir', fixture.reviewStatusDir,
          '--execution-pack-dir', fixture.executionPackDir,
          '--output-dir', outputDir,
        ],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('batch summary sourceTriage.path mismatch');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('fails on reviewed manifest base drift', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-artifact-consistency-base-'));
    const outputDir = join(sandbox, 'out');

    try {
      const fixture = createFixture(sandbox);
      const reviewedManifestPath = join(fixture.reviewedDir, 'reviewed-triage.json');
      const reviewedManifest = JSON.parse(readFileSync(reviewedManifestPath, 'utf8'));
      reviewedManifest.sourceInventory.base = 'origin/release';
      writeJson(reviewedManifestPath, reviewedManifest);

      const result = spawnSync(
        'node',
        [
          scriptPath,
          '--triage-json', fixture.triagePath,
          '--batch-dir', fixture.batchDir,
          '--reference-audit-dir', fixture.auditDir,
          '--reviewed-dir', fixture.reviewedDir,
          '--review-status-dir', fixture.reviewStatusDir,
          '--execution-pack-dir', fixture.executionPackDir,
          '--output-dir', outputDir,
        ],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('reviewed manifest sourceInventory.base mismatch');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('fails on post-apply count mismatch', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-artifact-consistency-count-'));
    const outputDir = join(sandbox, 'out');

    try {
      const fixture = createFixture(sandbox, { includePostApply: true });
      const postVerifySummary = JSON.parse(readFileSync(fixture.postVerifySummaryPath, 'utf8'));
      postVerifySummary.counts.verifiedAbsent = 2;
      writeJson(fixture.postVerifySummaryPath, postVerifySummary);

      const result = spawnSync(
        'node',
        [
          scriptPath,
          '--triage-json', fixture.triagePath,
          '--batch-dir', fixture.batchDir,
          '--reference-audit-dir', fixture.auditDir,
          '--reviewed-dir', fixture.reviewedDir,
          '--review-status-dir', fixture.reviewStatusDir,
          '--execution-pack-dir', fixture.executionPackDir,
          '--post-verify-summary-json', fixture.postVerifySummaryPath,
          '--output-dir', outputDir,
        ],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('post-apply verifiedAbsent+stillPresent mismatch');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
