import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/maintenance/remote-cleanup-closeout-summary.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

const createReviewStatusSummary = (overrides = {}) => ({
  generatedAt: '2026-03-08T00:00:00Z',
  source: {
    reviewedManifestPath: '/tmp/remote-cleanup-reviewed/reviewed-triage.json',
    referenceAuditDir: '/tmp/remote-cleanup-reference-audit',
    sourceTriagePath: '/tmp/remote-branch-triage.json',
  },
  overall: {
    'delete-ready': 2,
    'delete-blocked': 1,
    retained: 3,
    'pending-review': 0,
    'missing-audit': 0,
  },
  batches: {
    B: { id: 'B', total: 4 },
    C: { id: 'C', total: 2 },
  },
  ...overrides,
});

const createExecutionPackSummary = (overrides = {}) => ({
  generatedAt: '2026-03-08T00:10:00Z',
  source: {
    reviewStatusDir: '/tmp/remote-cleanup-review-status',
    reviewedManifestPath: '/tmp/remote-cleanup-reviewed/reviewed-triage.json',
    sourceTriagePath: '/tmp/remote-branch-triage.json',
    referenceAuditDir: '/tmp/remote-cleanup-reference-audit',
  },
  sourceInventory: {
    path: '/tmp/branch-inventory.json',
    generatedAt: '2026-03-07T23:50:00Z',
    base: 'origin/main',
    remote: 'origin',
  },
  deleteReady: {
    count: 2,
  },
  dryRun: {
    planned: 2,
    blocked: 0,
    stdout: 'dry-run ok',
  },
  ...overrides,
});

const createAmbiguousEvidenceSummary = (overrides = {}) => ({
  generatedAt: '2026-03-08T00:15:00Z',
  source: {
    batchJsonPath: '/tmp/remote-cleanup-batches/batch-c-ambiguous-stale.json',
    auditJsonPath: '/tmp/remote-cleanup-reference-audit/batch-c-ambiguous-stale.audit.json',
    sourceTriage: {
      path: '/tmp/remote-branch-triage.json',
    },
  },
  counts: {
    total: 2,
    reviewHints: {
      'keep-review': 1,
      'manual-review': 1,
    },
    withOpenIssueRefs: 1,
    withAutomationRefs: 0,
    withPlanRefs: 0,
    withCodeRefs: 0,
    clearOfActiveRefs: 1,
  },
  ...overrides,
});

const createPostVerifySummary = (overrides = {}) => ({
  generatedAt: '2026-03-08T00:20:00Z',
  source: {
    cleanupReportPath: '/tmp/branch-cleanup-report.json',
  },
  remoteName: 'origin',
  scope: 'remote',
  counts: {
    reportedDeleted: 2,
    verifiedAbsent: 2,
    stillPresent: 0,
    presentOnRemote: 0,
    recreatedRefs: 0,
    failedDeletes: 0,
    blocked: 0,
    plannedButNotDeleted: 0,
  },
  ...overrides,
});

const createRefreshAuditSummary = (postVerifySummaryPath: string, overrides = {}) => ({
  generatedAt: '2026-03-08T00:30:00Z',
  source: {
    postVerifySummaryPath,
    refreshedTriagePath: '/tmp/remote-branch-triage.json',
  },
  counts: {
    verifiedAbsentInput: 2,
    confirmedRemoved: 2,
    reappearedInTriage: 0,
    recreatedRefInput: 0,
    recreatedRefInTriage: 0,
    recreatedRefOutsideTriage: 0,
    refreshedRemoteMerged: 10,
    refreshedRemoteStale: 12,
  },
  ...overrides,
});

const createArtifactConsistencySummary = (overrides = {}) => ({
  generatedAt: '2026-03-08T00:40:00Z',
  counts: {
    reviewStatus: {
      'delete-ready': 2,
      'delete-blocked': 1,
      'pending-review': 0,
    },
    executionPack: {
      approvedBranches: 2,
      dryRunPlanned: 2,
      dryRunBlocked: 0,
    },
  },
  optional: {
    postApplyVerify: { available: true },
    refreshAudit: { available: true },
  },
  ...overrides,
});

const writeJson = (targetPath: string, payload: unknown) => {
  writeFileSync(targetPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
};

const runScript = (args: string[], cwd = repoRoot) =>
  spawnSync('node', [scriptPath, ...args], {
    cwd,
    encoding: 'utf8',
    timeout: 120_000,
  });

describe.sequential('remote-cleanup-closeout-summary script', () => {
  it('parses defaults and classifies review-pending state', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs([])).toMatchObject({
      reviewStatusSummaryJson: 'tmp/maintenance/remote-cleanup-review-status/summary.json',
      executionPackSummaryJson: 'tmp/maintenance/remote-cleanup-execution-pack/summary.json',
      outputDir: 'tmp/maintenance/remote-cleanup-closeout-summary',
    });
    expect(() => mod.parseArgs(['--execution-pack-summary-json', '--output-dir', 'tmp/out'])).toThrow(
      '--execution-pack-summary-json requires a value',
    );

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-closeout-pending-'));
    const reviewStatusPath = join(sandbox, 'review-status.summary.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeJson(
        reviewStatusPath,
        createReviewStatusSummary({
          overall: {
            'delete-ready': 1,
            'delete-blocked': 0,
            retained: 0,
            'pending-review': 2,
            'missing-audit': 1,
          },
        }),
      );

      const result = runScript(['--review-status-summary-json', reviewStatusPath, '--output-dir', outputDir]);
      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('nextAction=review-pending');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.stage).toBe('review-status');
      expect(summary.nextAction).toBe('review-pending');
      expect(summary.reasons[0]).toContain('review is incomplete');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('requests execution-pack rendering when delete-ready rows exist without a pack', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-closeout-render-pack-'));
    const reviewStatusPath = join(sandbox, 'review-status.summary.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeJson(reviewStatusPath, createReviewStatusSummary());

      const result = runScript(['--review-status-summary-json', reviewStatusPath, '--output-dir', outputDir]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.stage).toBe('review-status');
      expect(summary.nextAction).toBe('render-execution-pack');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('classifies apply-ready state when execution-pack is available', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-closeout-apply-ready-'));
    const reviewStatusPath = join(sandbox, 'review-status.summary.json');
    const executionPackPath = join(sandbox, 'execution-pack.summary.json');
    const ambiguousEvidencePath = join(sandbox, 'ambiguous-evidence.summary.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeJson(reviewStatusPath, createReviewStatusSummary());
      writeJson(executionPackPath, createExecutionPackSummary());
      writeJson(ambiguousEvidencePath, createAmbiguousEvidenceSummary());

      const result = runScript([
        '--review-status-summary-json',
        reviewStatusPath,
        '--execution-pack-summary-json',
        executionPackPath,
        '--ambiguous-evidence-summary-json',
        ambiguousEvidencePath,
        '--output-dir',
        outputDir,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.stage).toBe('execution-pack');
      expect(summary.nextAction).toBe('operator-apply');
      expect(summary.artifacts.ambiguousEvidence.available).toBe(true);
      expect(summary.counts.executionPack).toMatchObject({
        deleteReady: 2,
        dryRunPlanned: 2,
        dryRunBlocked: 0,
      });
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('requests investigation when post-apply verification still has unresolved refs', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-closeout-investigate-'));
    const reviewStatusPath = join(sandbox, 'review-status.summary.json');
    const executionPackPath = join(sandbox, 'execution-pack.summary.json');
    const postVerifyPath = join(sandbox, 'post-verify.summary.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeJson(reviewStatusPath, createReviewStatusSummary());
      writeJson(executionPackPath, createExecutionPackSummary());
      writeJson(
        postVerifyPath,
        createPostVerifySummary({
          counts: {
            reportedDeleted: 2,
            verifiedAbsent: 1,
            stillPresent: 0,
            presentOnRemote: 1,
            recreatedRefs: 1,
            failedDeletes: 0,
            blocked: 0,
            plannedButNotDeleted: 0,
          },
        }),
      );

      const result = runScript([
        '--review-status-summary-json',
        reviewStatusPath,
        '--execution-pack-summary-json',
        executionPackPath,
        '--post-verify-summary-json',
        postVerifyPath,
        '--output-dir',
        outputDir,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.stage).toBe('post-apply-verify');
      expect(summary.nextAction).toBe('investigate-still-present');
      expect(summary.reasons[0]).toContain('1 recreated');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('requests triage refresh after a clean post-apply verification', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-closeout-refresh-'));
    const reviewStatusPath = join(sandbox, 'review-status.summary.json');
    const executionPackPath = join(sandbox, 'execution-pack.summary.json');
    const postVerifyPath = join(sandbox, 'post-verify.summary.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeJson(reviewStatusPath, createReviewStatusSummary());
      writeJson(executionPackPath, createExecutionPackSummary());
      writeJson(postVerifyPath, createPostVerifySummary());

      const result = runScript([
        '--review-status-summary-json',
        reviewStatusPath,
        '--execution-pack-summary-json',
        executionPackPath,
        '--post-verify-summary-json',
        postVerifyPath,
        '--output-dir',
        outputDir,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.stage).toBe('post-apply-verify');
      expect(summary.nextAction).toBe('refresh-triage');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('classifies closeout-ready when refresh audit confirms clean closure', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-closeout-ready-'));
    const reviewStatusPath = join(sandbox, 'review-status.summary.json');
    const executionPackPath = join(sandbox, 'execution-pack.summary.json');
    const postVerifyPath = join(sandbox, 'post-verify.summary.json');
    const refreshAuditPath = join(sandbox, 'refresh-audit.summary.json');
    const artifactConsistencyPath = join(sandbox, 'artifact-consistency.summary.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeJson(reviewStatusPath, createReviewStatusSummary());
      writeJson(executionPackPath, createExecutionPackSummary());
      writeJson(postVerifyPath, createPostVerifySummary());
      writeJson(refreshAuditPath, createRefreshAuditSummary(postVerifyPath));
      writeJson(artifactConsistencyPath, createArtifactConsistencySummary());

      const result = runScript([
        '--review-status-summary-json',
        reviewStatusPath,
        '--execution-pack-summary-json',
        executionPackPath,
        '--post-verify-summary-json',
        postVerifyPath,
        '--refresh-audit-summary-json',
        refreshAuditPath,
        '--artifact-consistency-summary-json',
        artifactConsistencyPath,
        '--output-dir',
        outputDir,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.stage).toBe('closeout');
      expect(summary.nextAction).toBe('closeout-ready');
      expect(summary.artifacts.artifactConsistency.available).toBe(true);

      const issueComment = readFileSync(join(outputDir, 'issue-comment.md'), 'utf8');
      expect(issueComment).toContain('next action: closeout-ready');
      expect(issueComment).toContain('refresh audit: confirmed=2, reappeared=0, recreated=0');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('accepts relocated refresh-audit artifacts when counts still match the selected post-verify summary', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-closeout-relocated-refresh-'));
    const reviewStatusPath = join(sandbox, 'review-status.summary.json');
    const executionPackPath = join(sandbox, 'execution-pack.summary.json');
    const postVerifyPath = join(sandbox, 'post-verify.summary.json');
    const refreshAuditPath = join(sandbox, 'relocated-refresh-audit.summary.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeJson(reviewStatusPath, createReviewStatusSummary());
      writeJson(executionPackPath, createExecutionPackSummary());
      writeJson(postVerifyPath, createPostVerifySummary());
      writeJson(
        refreshAuditPath,
        createRefreshAuditSummary('/tmp/copied/post-verify.summary.json'),
      );

      const result = runScript([
        '--review-status-summary-json',
        reviewStatusPath,
        '--execution-pack-summary-json',
        executionPackPath,
        '--post-verify-summary-json',
        postVerifyPath,
        '--refresh-audit-summary-json',
        refreshAuditPath,
        '--output-dir',
        outputDir,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.nextAction).toBe('closeout-ready');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects inconsistent optional artifacts', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-closeout-mismatch-'));
    const reviewStatusPath = join(sandbox, 'review-status.summary.json');
    const executionPackPath = join(sandbox, 'execution-pack.summary.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeJson(reviewStatusPath, createReviewStatusSummary());
      writeJson(
        executionPackPath,
        createExecutionPackSummary({
          source: {
            reviewStatusDir: '/tmp/remote-cleanup-review-status',
            reviewedManifestPath: '/tmp/remote-cleanup-reviewed/reviewed-triage.json',
            sourceTriagePath: '/tmp/other-triage.json',
            referenceAuditDir: '/tmp/remote-cleanup-reference-audit',
          },
        }),
      );

      const result = runScript([
        '--review-status-summary-json',
        reviewStatusPath,
        '--execution-pack-summary-json',
        executionPackPath,
        '--output-dir',
        outputDir,
      ]);
      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('execution-pack source triage does not match review-status summary');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects stale post-verify summaries that do not match the current execution-pack counts', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-closeout-stale-post-verify-'));
    const reviewStatusPath = join(sandbox, 'review-status.summary.json');
    const executionPackPath = join(sandbox, 'execution-pack.summary.json');
    const postVerifyPath = join(sandbox, 'post-verify.summary.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeJson(reviewStatusPath, createReviewStatusSummary());
      writeJson(executionPackPath, createExecutionPackSummary());
      writeJson(
        postVerifyPath,
        createPostVerifySummary({
          counts: {
            reportedDeleted: 1,
            verifiedAbsent: 1,
            stillPresent: 0,
            presentOnRemote: 0,
            recreatedRefs: 0,
            failedDeletes: 0,
            blocked: 0,
            plannedButNotDeleted: 0,
          },
        }),
      );

      const result = runScript([
        '--review-status-summary-json',
        reviewStatusPath,
        '--execution-pack-summary-json',
        executionPackPath,
        '--post-verify-summary-json',
        postVerifyPath,
        '--output-dir',
        outputDir,
      ]);
      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain(
        'post-verify tracked delete-ready rows do not match execution-pack delete-ready count',
      );
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
