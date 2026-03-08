#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { renderTable } from './remote-branch-triage.mjs';

const DEFAULT_REVIEW_STATUS_SUMMARY_JSON = 'tmp/maintenance/remote-cleanup-review-status/summary.json';
const DEFAULT_EXECUTION_PACK_SUMMARY_JSON = 'tmp/maintenance/remote-cleanup-execution-pack/summary.json';
const DEFAULT_AMBIGUOUS_EVIDENCE_SUMMARY_JSON = 'tmp/maintenance/remote-cleanup-ambiguous-evidence/summary.json';
const DEFAULT_POST_VERIFY_SUMMARY_JSON = 'tmp/maintenance/remote-cleanup-post-apply-verify/summary.json';
const DEFAULT_REFRESH_AUDIT_SUMMARY_JSON = 'tmp/maintenance/remote-cleanup-refresh-audit/summary.json';
const DEFAULT_ARTIFACT_CONSISTENCY_SUMMARY_JSON = 'tmp/maintenance/remote-cleanup-artifact-consistency/summary.json';
const DEFAULT_OUTPUT_DIR = 'tmp/maintenance/remote-cleanup-closeout-summary';

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-cleanup-closeout-summary.mjs [options]

Options:
  --review-status-summary-json <path>         Review-status summary JSON (default: ${DEFAULT_REVIEW_STATUS_SUMMARY_JSON})
  --execution-pack-summary-json <path>        Optional execution-pack summary JSON (default: ${DEFAULT_EXECUTION_PACK_SUMMARY_JSON})
  --ambiguous-evidence-summary-json <path>    Optional ambiguous-evidence summary JSON (default: ${DEFAULT_AMBIGUOUS_EVIDENCE_SUMMARY_JSON})
  --post-verify-summary-json <path>           Optional post-apply verification summary JSON (default: ${DEFAULT_POST_VERIFY_SUMMARY_JSON})
  --refresh-audit-summary-json <path>         Optional refresh-audit summary JSON (default: ${DEFAULT_REFRESH_AUDIT_SUMMARY_JSON})
  --artifact-consistency-summary-json <path>  Optional artifact-consistency summary JSON (default: ${DEFAULT_ARTIFACT_CONSISTENCY_SUMMARY_JSON})
  --output-dir <path>                         Output directory (default: ${DEFAULT_OUTPUT_DIR})
  --help                                      Show this help
`);
};

const readRequiredValue = (argv, index, flag) => {
  const next = argv[index + 1];
  const value = typeof next === 'string' ? next.trim() : '';
  if (!value || value.startsWith('--')) {
    throw new Error(`${flag} requires a value`);
  }
  return value;
};

export const parseArgs = (argv) => {
  const options = {
    reviewStatusSummaryJson: DEFAULT_REVIEW_STATUS_SUMMARY_JSON,
    executionPackSummaryJson: DEFAULT_EXECUTION_PACK_SUMMARY_JSON,
    ambiguousEvidenceSummaryJson: DEFAULT_AMBIGUOUS_EVIDENCE_SUMMARY_JSON,
    postVerifySummaryJson: DEFAULT_POST_VERIFY_SUMMARY_JSON,
    refreshAuditSummaryJson: DEFAULT_REFRESH_AUDIT_SUMMARY_JSON,
    artifactConsistencySummaryJson: DEFAULT_ARTIFACT_CONSISTENCY_SUMMARY_JSON,
    outputDir: DEFAULT_OUTPUT_DIR,
    explicitOptional: {
      executionPackSummaryJson: false,
      ambiguousEvidenceSummaryJson: false,
      postVerifySummaryJson: false,
      refreshAuditSummaryJson: false,
      artifactConsistencySummaryJson: false,
    },
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--review-status-summary-json') {
      options.reviewStatusSummaryJson = readRequiredValue(argv, index, '--review-status-summary-json');
      index += 1;
      continue;
    }
    if (arg === '--execution-pack-summary-json') {
      options.executionPackSummaryJson = readRequiredValue(argv, index, '--execution-pack-summary-json');
      options.explicitOptional.executionPackSummaryJson = true;
      index += 1;
      continue;
    }
    if (arg === '--ambiguous-evidence-summary-json') {
      options.ambiguousEvidenceSummaryJson = readRequiredValue(argv, index, '--ambiguous-evidence-summary-json');
      options.explicitOptional.ambiguousEvidenceSummaryJson = true;
      index += 1;
      continue;
    }
    if (arg === '--post-verify-summary-json') {
      options.postVerifySummaryJson = readRequiredValue(argv, index, '--post-verify-summary-json');
      options.explicitOptional.postVerifySummaryJson = true;
      index += 1;
      continue;
    }
    if (arg === '--refresh-audit-summary-json') {
      options.refreshAuditSummaryJson = readRequiredValue(argv, index, '--refresh-audit-summary-json');
      options.explicitOptional.refreshAuditSummaryJson = true;
      index += 1;
      continue;
    }
    if (arg === '--artifact-consistency-summary-json') {
      options.artifactConsistencySummaryJson = readRequiredValue(argv, index, '--artifact-consistency-summary-json');
      options.explicitOptional.artifactConsistencySummaryJson = true;
      index += 1;
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = readRequiredValue(argv, index, '--output-dir');
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.reviewStatusSummaryJson) throw new Error('--review-status-summary-json is required');
  if (!options.outputDir) throw new Error('--output-dir is required');
  return options;
};

const readJson = (targetPath) => JSON.parse(fs.readFileSync(targetPath, 'utf8'));

const writeFile = (targetPath, content) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
};

const ensureFile = (targetPath, label) => {
  const resolved = path.resolve(targetPath);
  if (!fs.existsSync(resolved) || !fs.statSync(resolved).isFile()) {
    throw new Error(`${label} does not exist: ${resolved}`);
  }
  return resolved;
};

const resolveOptionalFile = (targetPath, label, required) => {
  const resolved = path.resolve(targetPath);
  if (!fs.existsSync(resolved)) {
    if (required) {
      throw new Error(`${label} does not exist: ${resolved}`);
    }
    return null;
  }
  if (!fs.statSync(resolved).isFile()) {
    throw new Error(`${label} is not a file: ${resolved}`);
  }
  return resolved;
};

const ensureObject = (value, label) => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    throw new Error(`${label} must be an object`);
  }
  return value;
};

const ensureCount = (value, label) => {
  const numeric = Number(value);
  if (!Number.isInteger(numeric) || numeric < 0) {
    throw new Error(`${label} must be a non-negative integer`);
  }
  return numeric;
};

const maybeString = (value) => (value === null || value === undefined ? '' : String(value));

const normalizeReviewStatus = (summaryPath) => {
  const summary = readJson(summaryPath);
  const source = ensureObject(summary?.source, 'review-status source');
  const overall = ensureObject(summary?.overall, 'review-status overall');
  const batches = ensureObject(summary?.batches, 'review-status batches');
  const sourceTriagePath = maybeString(source.sourceTriagePath).trim();
  if (!sourceTriagePath) throw new Error('review-status source.sourceTriagePath is required');
  const reviewedManifestPath = maybeString(source.reviewedManifestPath).trim();
  if (!reviewedManifestPath) throw new Error('review-status source.reviewedManifestPath is required');

  return {
    available: true,
    path: summaryPath,
    generatedAt: maybeString(summary?.generatedAt).trim(),
    source: {
      reviewedManifestPath,
      referenceAuditDir: maybeString(source.referenceAuditDir).trim(),
      sourceTriagePath,
    },
    counts: {
      deleteReady: ensureCount(overall['delete-ready'], 'review-status overall.delete-ready'),
      deleteBlocked: ensureCount(overall['delete-blocked'], 'review-status overall.delete-blocked'),
      retained: ensureCount(overall.retained, 'review-status overall.retained'),
      pendingReview: ensureCount(overall['pending-review'], 'review-status overall.pending-review'),
      missingAudit: ensureCount(overall['missing-audit'], 'review-status overall.missing-audit'),
      batchBTotal: ensureCount(batches?.B?.total || 0, 'review-status batches.B.total'),
      batchCTotal: ensureCount(batches?.C?.total || 0, 'review-status batches.C.total'),
    },
    raw: summary,
  };
};

const normalizeExecutionPack = (summaryPath) => {
  const summary = readJson(summaryPath);
  const source = ensureObject(summary?.source, 'execution-pack source');
  const sourceInventory = ensureObject(summary?.sourceInventory, 'execution-pack sourceInventory');
  const deleteReady = ensureObject(summary?.deleteReady, 'execution-pack deleteReady');
  const dryRun = ensureObject(summary?.dryRun, 'execution-pack dryRun');

  return {
    available: true,
    path: summaryPath,
    generatedAt: maybeString(summary?.generatedAt).trim(),
    source: {
      reviewStatusDir: maybeString(source.reviewStatusDir).trim(),
      reviewedManifestPath: maybeString(source.reviewedManifestPath).trim(),
      sourceTriagePath: maybeString(source.sourceTriagePath).trim(),
      referenceAuditDir: maybeString(source.referenceAuditDir).trim(),
    },
    sourceInventory: {
      path: maybeString(sourceInventory.path).trim(),
      generatedAt: maybeString(sourceInventory.generatedAt).trim(),
      base: maybeString(sourceInventory.base).trim(),
      remote: maybeString(sourceInventory.remote).trim(),
    },
    counts: {
      deleteReady: ensureCount(deleteReady.count, 'execution-pack deleteReady.count'),
      dryRunPlanned: ensureCount(dryRun.planned, 'execution-pack dryRun.planned'),
      dryRunBlocked: ensureCount(dryRun.blocked, 'execution-pack dryRun.blocked'),
    },
    raw: summary,
  };
};

const normalizeAmbiguousEvidence = (summaryPath) => {
  const summary = readJson(summaryPath);
  const source = ensureObject(summary?.source, 'ambiguous-evidence source');
  const counts = ensureObject(summary?.counts, 'ambiguous-evidence counts');
  const reviewHints = ensureObject(counts?.reviewHints, 'ambiguous-evidence counts.reviewHints');
  const sourceTriage = ensureObject(source?.sourceTriage, 'ambiguous-evidence source.sourceTriage');

  return {
    available: true,
    path: summaryPath,
    generatedAt: maybeString(summary?.generatedAt).trim(),
    source: {
      batchJsonPath: maybeString(source.batchJsonPath).trim(),
      auditJsonPath: maybeString(source.auditJsonPath).trim(),
      sourceTriagePath: maybeString(sourceTriage.path).trim(),
    },
    counts: {
      total: ensureCount(counts.total, 'ambiguous-evidence counts.total'),
      keepReview: ensureCount(reviewHints['keep-review'], 'ambiguous-evidence counts.reviewHints.keep-review'),
      manualReview: ensureCount(reviewHints['manual-review'], 'ambiguous-evidence counts.reviewHints.manual-review'),
      withOpenIssueRefs: ensureCount(counts.withOpenIssueRefs, 'ambiguous-evidence counts.withOpenIssueRefs'),
      withAutomationRefs: ensureCount(counts.withAutomationRefs, 'ambiguous-evidence counts.withAutomationRefs'),
      withPlanRefs: ensureCount(counts.withPlanRefs, 'ambiguous-evidence counts.withPlanRefs'),
      withCodeRefs: ensureCount(counts.withCodeRefs, 'ambiguous-evidence counts.withCodeRefs'),
      clearOfActiveRefs: ensureCount(counts.clearOfActiveRefs, 'ambiguous-evidence counts.clearOfActiveRefs'),
    },
    raw: summary,
  };
};

const normalizePostVerify = (summaryPath) => {
  const summary = readJson(summaryPath);
  const source = ensureObject(summary?.source, 'post-verify source');
  const counts = ensureObject(summary?.counts, 'post-verify counts');
  const selection = ensureObject(summary?.selection || {}, 'post-verify selection');

  return {
    available: true,
    path: summaryPath,
    generatedAt: maybeString(summary?.generatedAt).trim(),
    source: {
      cleanupReportPath: maybeString(source.cleanupReportPath).trim(),
    },
    remoteName: maybeString(summary?.remoteName).trim(),
    scope: maybeString(summary?.scope).trim(),
    selection: {
      mode: maybeString(selection.mode).trim(),
      sourcePath: maybeString(selection.sourcePath).trim(),
      expectedBase: maybeString(selection.expectedBase).trim(),
      expectedRemote: maybeString(selection.expectedRemote).trim(),
    },
    counts: {
      reportedDeleted: ensureCount(counts.reportedDeleted, 'post-verify counts.reportedDeleted'),
      verifiedAbsent: ensureCount(counts.verifiedAbsent, 'post-verify counts.verifiedAbsent'),
      stillPresent: ensureCount(counts.stillPresent, 'post-verify counts.stillPresent'),
      failedDeletes: ensureCount(counts.failedDeletes, 'post-verify counts.failedDeletes'),
      blocked: ensureCount(counts.blocked, 'post-verify counts.blocked'),
      plannedButNotDeleted: ensureCount(counts.plannedButNotDeleted, 'post-verify counts.plannedButNotDeleted'),
    },
    raw: summary,
  };
};

const normalizeRefreshAudit = (summaryPath) => {
  const summary = readJson(summaryPath);
  const source = ensureObject(summary?.source, 'refresh-audit source');
  const counts = ensureObject(summary?.counts, 'refresh-audit counts');

  return {
    available: true,
    path: summaryPath,
    generatedAt: maybeString(summary?.generatedAt).trim(),
    source: {
      postVerifySummaryPath: maybeString(source.postVerifySummaryPath).trim(),
      refreshedTriagePath: maybeString(source.refreshedTriagePath).trim(),
    },
    counts: {
      verifiedAbsentInput: ensureCount(counts.verifiedAbsentInput, 'refresh-audit counts.verifiedAbsentInput'),
      confirmedRemoved: ensureCount(counts.confirmedRemoved, 'refresh-audit counts.confirmedRemoved'),
      reappearedInTriage: ensureCount(counts.reappearedInTriage, 'refresh-audit counts.reappearedInTriage'),
      refreshedRemoteMerged: ensureCount(counts.refreshedRemoteMerged, 'refresh-audit counts.refreshedRemoteMerged'),
      refreshedRemoteStale: ensureCount(counts.refreshedRemoteStale, 'refresh-audit counts.refreshedRemoteStale'),
    },
    raw: summary,
  };
};

const normalizeArtifactConsistency = (summaryPath) => {
  const summary = readJson(summaryPath);
  const counts = ensureObject(summary?.counts, 'artifact-consistency counts');
  const reviewStatus = ensureObject(counts?.reviewStatus, 'artifact-consistency counts.reviewStatus');
  const executionPack = ensureObject(counts?.executionPack, 'artifact-consistency counts.executionPack');
  const optional = ensureObject(summary?.optional || {}, 'artifact-consistency optional');

  return {
    available: true,
    path: summaryPath,
    generatedAt: maybeString(summary?.generatedAt).trim(),
    counts: {
      reviewStatus: {
        deleteReady: ensureCount(reviewStatus['delete-ready'], 'artifact-consistency counts.reviewStatus.delete-ready'),
        deleteBlocked: ensureCount(reviewStatus['delete-blocked'], 'artifact-consistency counts.reviewStatus.delete-blocked'),
        pendingReview: ensureCount(reviewStatus['pending-review'], 'artifact-consistency counts.reviewStatus.pending-review'),
      },
      executionPack: {
        approvedBranches: ensureCount(executionPack.approvedBranches, 'artifact-consistency counts.executionPack.approvedBranches'),
        dryRunPlanned: ensureCount(executionPack.dryRunPlanned, 'artifact-consistency counts.executionPack.dryRunPlanned'),
        dryRunBlocked: ensureCount(executionPack.dryRunBlocked, 'artifact-consistency counts.executionPack.dryRunBlocked'),
      },
      postApplyVerifyAvailable: Boolean(optional?.postApplyVerify?.available),
      refreshAuditAvailable: Boolean(optional?.refreshAudit?.available),
    },
    raw: summary,
  };
};

const unavailableSummary = (pathValue) => ({
  available: false,
  path: pathValue || '',
});

const loadOptionalSummary = (targetPath, explicit, label, loader) => {
  const resolved = resolveOptionalFile(targetPath, label, explicit);
  if (!resolved) return unavailableSummary(path.resolve(targetPath));
  return loader(resolved);
};

const ensurePostVerifyMatchesExecutionPack = (postVerify, executionPack) => {
  if (!executionPack.available || !postVerify.available) return;

  if (postVerify.remoteName && postVerify.remoteName !== executionPack.sourceInventory.remote) {
    throw new Error('post-verify remote does not match execution-pack source inventory remote');
  }
  if (postVerify.selection.expectedRemote && postVerify.selection.expectedRemote !== executionPack.sourceInventory.remote) {
    throw new Error('post-verify expectedRemote does not match execution-pack source inventory remote');
  }
  if (postVerify.selection.expectedBase && postVerify.selection.expectedBase !== executionPack.sourceInventory.base) {
    throw new Error('post-verify expectedBase does not match execution-pack source inventory base');
  }

  const trackedDeleteReady =
    postVerify.counts.reportedDeleted +
    postVerify.counts.failedDeletes +
    postVerify.counts.blocked +
    postVerify.counts.plannedButNotDeleted;
  if (trackedDeleteReady !== executionPack.counts.deleteReady) {
    throw new Error('post-verify tracked delete-ready rows do not match execution-pack delete-ready count');
  }

  const trackedPlanned =
    postVerify.counts.reportedDeleted +
    postVerify.counts.failedDeletes +
    postVerify.counts.plannedButNotDeleted;
  if (trackedPlanned !== executionPack.counts.dryRunPlanned) {
    throw new Error('post-verify planned rows do not match execution-pack dry-run planned count');
  }
  if (postVerify.counts.blocked !== executionPack.counts.dryRunBlocked) {
    throw new Error('post-verify blocked rows do not match execution-pack dry-run blocked count');
  }
};

const validateConsistency = (reviewStatus, executionPack, ambiguousEvidence, postVerify, refreshAudit, artifactConsistency) => {
  if (executionPack.available) {
    if (executionPack.source.reviewedManifestPath !== reviewStatus.source.reviewedManifestPath) {
      throw new Error('execution-pack reviewed manifest does not match review-status summary');
    }
    if (executionPack.source.sourceTriagePath !== reviewStatus.source.sourceTriagePath) {
      throw new Error('execution-pack source triage does not match review-status summary');
    }
    if (executionPack.counts.deleteReady !== reviewStatus.counts.deleteReady) {
      throw new Error('execution-pack delete-ready count does not match review-status summary');
    }
  }

  if (ambiguousEvidence.available && ambiguousEvidence.source.sourceTriagePath !== reviewStatus.source.sourceTriagePath) {
    throw new Error('ambiguous-evidence source triage does not match review-status summary');
  }

  ensurePostVerifyMatchesExecutionPack(postVerify, executionPack);

  if (refreshAudit.available && !postVerify.available) {
    throw new Error('refresh-audit requires a matching post-verify summary');
  }
  if (refreshAudit.available && postVerify.available) {
    if (refreshAudit.counts.verifiedAbsentInput !== postVerify.counts.verifiedAbsent) {
      throw new Error('refresh-audit verifiedAbsentInput does not match post-verify verifiedAbsent count');
    }
    if (
      refreshAudit.counts.confirmedRemoved + refreshAudit.counts.reappearedInTriage !==
      refreshAudit.counts.verifiedAbsentInput
    ) {
      throw new Error('refresh-audit counts do not sum to verifiedAbsentInput');
    }
  }

  if (artifactConsistency.available) {
    if (artifactConsistency.counts.reviewStatus.deleteReady !== reviewStatus.counts.deleteReady) {
      throw new Error('artifact-consistency delete-ready count does not match review-status summary');
    }
    if (artifactConsistency.counts.reviewStatus.deleteBlocked !== reviewStatus.counts.deleteBlocked) {
      throw new Error('artifact-consistency delete-blocked count does not match review-status summary');
    }
    if (artifactConsistency.counts.reviewStatus.pendingReview !== reviewStatus.counts.pendingReview) {
      throw new Error('artifact-consistency pending-review count does not match review-status summary');
    }
    if (executionPack.available) {
      if (artifactConsistency.counts.executionPack.approvedBranches !== executionPack.counts.deleteReady) {
        throw new Error('artifact-consistency approvedBranches does not match execution-pack delete-ready count');
      }
      if (artifactConsistency.counts.executionPack.dryRunPlanned !== executionPack.counts.dryRunPlanned) {
        throw new Error('artifact-consistency dryRunPlanned does not match execution-pack summary');
      }
      if (artifactConsistency.counts.executionPack.dryRunBlocked !== executionPack.counts.dryRunBlocked) {
        throw new Error('artifact-consistency dryRunBlocked does not match execution-pack summary');
      }
    }
  }
};

const classifyStage = ({ reviewStatus, executionPack, postVerify, refreshAudit }) => {
  const reasons = [];
  const pendingItems = reviewStatus.counts.pendingReview + reviewStatus.counts.missingAudit;

  if (pendingItems > 0) {
    reasons.push(`review is incomplete (${reviewStatus.counts.pendingReview} pending, ${reviewStatus.counts.missingAudit} missing audit)`);
    return {
      stage: 'review-status',
      nextAction: 'review-pending',
      reasons,
    };
  }

  if (reviewStatus.counts.deleteReady > 0 && !executionPack.available) {
    reasons.push(`${reviewStatus.counts.deleteReady} delete-ready branches remain, but no execution pack is available`);
    return {
      stage: 'review-status',
      nextAction: 'render-execution-pack',
      reasons,
    };
  }

  if (reviewStatus.counts.deleteReady > 0 && executionPack.available && !postVerify.available) {
    if (executionPack.counts.dryRunPlanned > 0) {
      reasons.push(`execution pack is ready (${executionPack.counts.dryRunPlanned} planned, ${executionPack.counts.dryRunBlocked} blocked)`);
      return {
        stage: 'execution-pack',
        nextAction: 'operator-apply',
        reasons,
      };
    }
    reasons.push(`execution pack exists, but dry-run planned 0 and blocked ${executionPack.counts.dryRunBlocked}`);
    return {
      stage: 'execution-pack',
      nextAction: 'investigate-still-present',
      reasons,
    };
  }

  if (postVerify.available) {
    const unresolved = postVerify.counts.stillPresent + postVerify.counts.failedDeletes + postVerify.counts.plannedButNotDeleted + postVerify.counts.blocked;
    if (unresolved > 0) {
      reasons.push(
        `post-apply verification still has follow-up (${postVerify.counts.stillPresent} still present, ${postVerify.counts.failedDeletes} failed, ${postVerify.counts.plannedButNotDeleted} planned-not-deleted, ${postVerify.counts.blocked} blocked)`,
      );
      return {
        stage: 'post-apply-verify',
        nextAction: 'investigate-still-present',
        reasons,
      };
    }
    if (!refreshAudit.available) {
      reasons.push(`post-apply verification is clean (${postVerify.counts.verifiedAbsent} verified absent), but refresh audit is missing`);
      return {
        stage: 'post-apply-verify',
        nextAction: 'refresh-triage',
        reasons,
      };
    }
  }

  if (refreshAudit.available) {
    if (refreshAudit.counts.reappearedInTriage > 0) {
      reasons.push(`${refreshAudit.counts.reappearedInTriage} branches reappeared in refreshed triage`);
      return {
        stage: 'refresh-audit',
        nextAction: 'investigate-still-present',
        reasons,
      };
    }
    reasons.push('refresh audit confirmed no branches reappeared in refreshed triage');
    return {
      stage: 'closeout',
      nextAction: 'closeout-ready',
      reasons,
    };
  }

  if (reviewStatus.counts.deleteReady === 0) {
    reasons.push('no delete-ready branches remain and no refresh follow-up is pending');
    return {
      stage: 'closeout',
      nextAction: 'closeout-ready',
      reasons,
    };
  }

  reasons.push('workflow state requires manual inspection');
  return {
    stage: 'review-status',
    nextAction: 'review-pending',
    reasons,
  };
};

const renderArtifactRows = (summary) =>
  [
    ['review-status', 'yes', String(summary.counts.reviewStatus.deleteReady), String(summary.counts.reviewStatus.pendingReview), path.basename(summary.artifacts.reviewStatus.path)],
    ['execution-pack', summary.artifacts.executionPack.available ? 'yes' : 'no', summary.artifacts.executionPack.available ? String(summary.counts.executionPack.dryRunPlanned) : '-', summary.artifacts.executionPack.available ? String(summary.counts.executionPack.dryRunBlocked) : '-', summary.artifacts.executionPack.available ? path.basename(summary.artifacts.executionPack.path) : '-'],
    ['ambiguous-evidence', summary.artifacts.ambiguousEvidence.available ? 'yes' : 'no', summary.artifacts.ambiguousEvidence.available ? String(summary.counts.ambiguousEvidence.total) : '-', summary.artifacts.ambiguousEvidence.available ? String(summary.counts.ambiguousEvidence.manualReview) : '-', summary.artifacts.ambiguousEvidence.available ? path.basename(summary.artifacts.ambiguousEvidence.path) : '-'],
    ['post-apply-verify', summary.artifacts.postVerify.available ? 'yes' : 'no', summary.artifacts.postVerify.available ? String(summary.counts.postVerify.verifiedAbsent) : '-', summary.artifacts.postVerify.available ? String(summary.counts.postVerify.stillPresent) : '-', summary.artifacts.postVerify.available ? path.basename(summary.artifacts.postVerify.path) : '-'],
    ['refresh-audit', summary.artifacts.refreshAudit.available ? 'yes' : 'no', summary.artifacts.refreshAudit.available ? String(summary.counts.refreshAudit.confirmedRemoved) : '-', summary.artifacts.refreshAudit.available ? String(summary.counts.refreshAudit.reappearedInTriage) : '-', summary.artifacts.refreshAudit.available ? path.basename(summary.artifacts.refreshAudit.path) : '-'],
    ['artifact-consistency', summary.artifacts.artifactConsistency.available ? 'yes' : 'no', summary.artifacts.artifactConsistency.available ? String(summary.counts.artifactConsistency.executionPack.approvedBranches) : '-', summary.artifacts.artifactConsistency.available ? String(summary.counts.artifactConsistency.executionPack.dryRunBlocked) : '-', summary.artifacts.artifactConsistency.available ? path.basename(summary.artifacts.artifactConsistency.path) : '-'],
  ];

const renderSummaryMarkdown = (summary) => {
  const artifactRows = renderArtifactRows(summary);

  return `# Remote Cleanup Closeout Summary

- generatedAt: ${summary.generatedAt}
- stage: \`${summary.stage}\`
- next action: \`${summary.nextAction}\`
- source triage: \`${summary.source.reviewStatus.sourceTriagePath}\`
- reviewed manifest: \`${summary.source.reviewStatus.reviewedManifestPath}\`

## Why this next action

${summary.reasons.map((reason) => `- ${reason}`).join('\n')}

## Review status

- delete-ready: ${summary.counts.reviewStatus.deleteReady}
- delete-blocked: ${summary.counts.reviewStatus.deleteBlocked}
- retained: ${summary.counts.reviewStatus.retained}
- pending-review: ${summary.counts.reviewStatus.pendingReview}
- missing-audit: ${summary.counts.reviewStatus.missingAudit}

## Artifact availability

${renderTable(['artifact', 'available', 'primary', 'secondary', 'file'], artifactRows)}
`;
};

const renderIssueComment = (summary) => {
  const lines = [
    `Remote cleanup closeout summary from \`${summary.source.reviewStatus.path}\`:`,
    `- stage: ${summary.stage}`,
    `- next action: ${summary.nextAction}`,
    `- review status: ready=${summary.counts.reviewStatus.deleteReady}, blocked=${summary.counts.reviewStatus.deleteBlocked}, pending=${summary.counts.reviewStatus.pendingReview}, missing-audit=${summary.counts.reviewStatus.missingAudit}`,
  ];

  if (summary.artifacts.executionPack.available) {
    lines.push(
      `- execution pack: planned=${summary.counts.executionPack.dryRunPlanned}, blocked=${summary.counts.executionPack.dryRunBlocked}`,
    );
  }
  if (summary.artifacts.ambiguousEvidence.available) {
    lines.push(
      `- ambiguous evidence: total=${summary.counts.ambiguousEvidence.total}, manual-review=${summary.counts.ambiguousEvidence.manualReview}, keep-review=${summary.counts.ambiguousEvidence.keepReview}`,
    );
  }
  if (summary.artifacts.postVerify.available) {
    lines.push(
      `- post-apply verify: verified=${summary.counts.postVerify.verifiedAbsent}, still-present=${summary.counts.postVerify.stillPresent}, failed=${summary.counts.postVerify.failedDeletes}, planned-not-deleted=${summary.counts.postVerify.plannedButNotDeleted}`,
    );
  }
  if (summary.artifacts.refreshAudit.available) {
    lines.push(
      `- refresh audit: confirmed=${summary.counts.refreshAudit.confirmedRemoved}, reappeared=${summary.counts.refreshAudit.reappearedInTriage}`,
    );
  }
  if (summary.artifacts.artifactConsistency.available) {
    lines.push(
      `- artifact consistency: approved=${summary.counts.artifactConsistency.executionPack.approvedBranches}, planned=${summary.counts.artifactConsistency.executionPack.dryRunPlanned}, blocked=${summary.counts.artifactConsistency.executionPack.dryRunBlocked}`,
    );
  }
  lines.push('', 'Reasons:');
  for (const reason of summary.reasons) {
    lines.push(`- ${reason}`);
  }
  return `${lines.join('\n')}\n`;
};

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const reviewStatusPath = ensureFile(options.reviewStatusSummaryJson, 'review-status summary');
  const reviewStatus = normalizeReviewStatus(reviewStatusPath);
  const executionPack = loadOptionalSummary(
    options.executionPackSummaryJson,
    options.explicitOptional.executionPackSummaryJson,
    'execution-pack summary',
    normalizeExecutionPack,
  );
  const ambiguousEvidence = loadOptionalSummary(
    options.ambiguousEvidenceSummaryJson,
    options.explicitOptional.ambiguousEvidenceSummaryJson,
    'ambiguous-evidence summary',
    normalizeAmbiguousEvidence,
  );
  const postVerify = loadOptionalSummary(
    options.postVerifySummaryJson,
    options.explicitOptional.postVerifySummaryJson,
    'post-verify summary',
    normalizePostVerify,
  );
  const refreshAudit = loadOptionalSummary(
    options.refreshAuditSummaryJson,
    options.explicitOptional.refreshAuditSummaryJson,
    'refresh-audit summary',
    normalizeRefreshAudit,
  );
  const artifactConsistency = loadOptionalSummary(
    options.artifactConsistencySummaryJson,
    options.explicitOptional.artifactConsistencySummaryJson,
    'artifact-consistency summary',
    normalizeArtifactConsistency,
  );

  validateConsistency(reviewStatus, executionPack, ambiguousEvidence, postVerify, refreshAudit, artifactConsistency);
  const stageState = classifyStage({ reviewStatus, executionPack, postVerify, refreshAudit });
  const outputDir = path.resolve(options.outputDir);

  const summary = {
    generatedAt: new Date().toISOString(),
    stage: stageState.stage,
    nextAction: stageState.nextAction,
    reasons: stageState.reasons,
    source: {
      reviewStatus: {
        path: reviewStatus.path,
        reviewedManifestPath: reviewStatus.source.reviewedManifestPath,
        sourceTriagePath: reviewStatus.source.sourceTriagePath,
        referenceAuditDir: reviewStatus.source.referenceAuditDir,
      },
    },
    artifacts: {
      reviewStatus: {
        available: true,
        path: reviewStatus.path,
      },
      executionPack: {
        available: executionPack.available,
        path: executionPack.path || '',
      },
      ambiguousEvidence: {
        available: ambiguousEvidence.available,
        path: ambiguousEvidence.path || '',
      },
      postVerify: {
        available: postVerify.available,
        path: postVerify.path || '',
      },
      refreshAudit: {
        available: refreshAudit.available,
        path: refreshAudit.path || '',
      },
      artifactConsistency: {
        available: artifactConsistency.available,
        path: artifactConsistency.path || '',
      },
    },
    counts: {
      reviewStatus: reviewStatus.counts,
      executionPack: executionPack.available ? executionPack.counts : null,
      ambiguousEvidence: ambiguousEvidence.available ? ambiguousEvidence.counts : null,
      postVerify: postVerify.available ? postVerify.counts : null,
      refreshAudit: refreshAudit.available ? refreshAudit.counts : null,
      artifactConsistency: artifactConsistency.available ? artifactConsistency.counts : null,
    },
  };

  writeFile(path.join(outputDir, 'summary.json'), `${JSON.stringify(summary, null, 2)}\n`);
  writeFile(path.join(outputDir, 'summary.md'), renderSummaryMarkdown(summary));
  writeFile(path.join(outputDir, 'issue-comment.md'), renderIssueComment(summary));

  console.log(`[remote-cleanup-closeout-summary] wrote ${path.join(outputDir, 'summary.json')}`);
  console.log(
    `[remote-cleanup-closeout-summary] stage=${summary.stage} nextAction=${summary.nextAction} ready=${summary.counts.reviewStatus.deleteReady} pending=${summary.counts.reviewStatus.pendingReview}`,
  );
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error('[remote-cleanup-closeout-summary] ERROR:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}
