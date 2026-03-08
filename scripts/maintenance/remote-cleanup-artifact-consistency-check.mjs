import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { LOW_RISK_PREFIXES } from './remote-branch-triage.mjs';

const DEFAULT_TRIAGE_JSON = 'tmp/maintenance/remote-branch-triage.json';
const DEFAULT_BATCH_DIR = 'tmp/maintenance/remote-cleanup-batches';
const DEFAULT_REFERENCE_AUDIT_DIR = 'tmp/maintenance/remote-cleanup-reference-audit';
const DEFAULT_REVIEWED_DIR = 'tmp/maintenance/remote-cleanup-reviewed';
const DEFAULT_REVIEW_STATUS_DIR = 'tmp/maintenance/remote-cleanup-review-status';
const DEFAULT_EXECUTION_PACK_DIR = 'tmp/maintenance/remote-cleanup-execution-pack';
const DEFAULT_POST_VERIFY_SUMMARY_JSON = 'tmp/maintenance/remote-cleanup-post-apply-verify/summary.json';
const DEFAULT_REFRESH_AUDIT_SUMMARY_JSON = 'tmp/maintenance/remote-cleanup-refresh-audit/summary.json';
const DEFAULT_OUTPUT_DIR = 'tmp/maintenance/remote-cleanup-artifact-consistency';
const REVIEW_STATUS_FILES = ['delete-ready', 'delete-blocked', 'pending-review', 'retained', 'missing-audit'];

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-cleanup-artifact-consistency-check.mjs [options]

Options:
  --triage-json <path>                  Remote branch triage JSON (default: ${DEFAULT_TRIAGE_JSON})
  --batch-dir <path>                    Remote cleanup batches directory (default: ${DEFAULT_BATCH_DIR})
  --reference-audit-dir <path>          Reference audit directory (default: ${DEFAULT_REFERENCE_AUDIT_DIR})
  --reviewed-dir <path>                 Reviewed triage directory (default: ${DEFAULT_REVIEWED_DIR})
  --review-status-dir <path>            Review status directory (default: ${DEFAULT_REVIEW_STATUS_DIR})
  --execution-pack-dir <path>           Execution pack directory (default: ${DEFAULT_EXECUTION_PACK_DIR})
  --post-verify-summary-json <path>     Optional post-apply verify summary (default: ${DEFAULT_POST_VERIFY_SUMMARY_JSON})
  --refresh-audit-summary-json <path>   Optional refresh-audit summary (default: ${DEFAULT_REFRESH_AUDIT_SUMMARY_JSON})
  --output-dir <path>                   Output directory (default: ${DEFAULT_OUTPUT_DIR})
  -h, --help                            Show help`);
};

export const parseArgs = (argv) => {
  const options = {
    triageJson: DEFAULT_TRIAGE_JSON,
    batchDir: DEFAULT_BATCH_DIR,
    referenceAuditDir: DEFAULT_REFERENCE_AUDIT_DIR,
    reviewedDir: DEFAULT_REVIEWED_DIR,
    reviewStatusDir: DEFAULT_REVIEW_STATUS_DIR,
    executionPackDir: DEFAULT_EXECUTION_PACK_DIR,
    postVerifySummaryJson: DEFAULT_POST_VERIFY_SUMMARY_JSON,
    refreshAuditSummaryJson: DEFAULT_REFRESH_AUDIT_SUMMARY_JSON,
    outputDir: DEFAULT_OUTPUT_DIR,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '-h' || arg === '--help') {
      usage();
      process.exit(0);
    }
    if (arg === '--triage-json') {
      options.triageJson = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--batch-dir') {
      options.batchDir = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--reference-audit-dir') {
      options.referenceAuditDir = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--reviewed-dir') {
      options.reviewedDir = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--review-status-dir') {
      options.reviewStatusDir = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--execution-pack-dir') {
      options.executionPackDir = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--post-verify-summary-json') {
      options.postVerifySummaryJson = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--refresh-audit-summary-json') {
      options.refreshAuditSummaryJson = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = String(argv[++index] || '').trim();
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  for (const [key, value] of Object.entries(options)) {
    if (!value) {
      throw new Error(`Missing value for ${key}`);
    }
  }

  return options;
};

const readJson = (targetPath) => JSON.parse(fs.readFileSync(targetPath, 'utf8'));

const ensureDir = (targetPath, label) => {
  const resolved = path.resolve(targetPath);
  if (!fs.existsSync(resolved) || !fs.statSync(resolved).isDirectory()) {
    throw new Error(`${label} does not exist: ${resolved}`);
  }
  return resolved;
};

const ensureFile = (targetPath, label) => {
  const resolved = path.resolve(targetPath);
  if (!fs.existsSync(resolved) || !fs.statSync(resolved).isFile()) {
    throw new Error(`${label} does not exist: ${resolved}`);
  }
  return resolved;
};

const resolveIfExists = (targetPath) => {
  const resolved = path.resolve(targetPath);
  if (!fs.existsSync(resolved) || !fs.statSync(resolved).isFile()) {
    return null;
  }
  return resolved;
};

const assert = (condition, message) => {
  if (!condition) {
    throw new Error(message);
  }
};

const resolveSamePath = (actualPath, expectedPath, label) => {
  assert(path.resolve(actualPath) === path.resolve(expectedPath), `${label} mismatch: expected ${path.resolve(expectedPath)}, got ${path.resolve(actualPath)}`);
};

const ensureArray = (value, label) => {
  assert(Array.isArray(value), `${label} must be an array`);
  return value;
};

const ensureObject = (value, label) => {
  assert(value && typeof value === 'object' && !Array.isArray(value), `${label} must be an object`);
  return value;
};

const ensureInteger = (value, label) => {
  assert(Number.isInteger(value) && value >= 0, `${label} must be a non-negative integer`);
  return value;
};

const countBatchB = (remoteStale) =>
  remoteStale.filter((item) => LOW_RISK_PREFIXES.some((prefix) => String(item?.branch || '').startsWith(prefix)) && item?.prState !== 'ambiguous').length;

const countBatchC = (remoteStale) => remoteStale.filter((item) => item?.prState === 'ambiguous').length;

const countStatus = (items, status) => items.filter((item) => String(item?.status || '') === status).length;

const renderTable = (headers, rows) => {
  const lines = [
    `| ${headers.join(' | ')} |`,
    `| ${headers.map(() => '---').join(' | ')} |`,
    ...rows.map((row) => `| ${row.map((cell) => String(cell ?? '-')).join(' | ')} |`),
  ];
  return `${lines.join('\n')}\n`;
};

const loadCoreArtifacts = (options) => {
  const triageJsonPath = ensureFile(options.triageJson, 'triage JSON');
  const batchDir = ensureDir(options.batchDir, 'batch directory');
  const referenceAuditDir = ensureDir(options.referenceAuditDir, 'reference audit directory');
  const reviewedDir = ensureDir(options.reviewedDir, 'reviewed directory');
  const reviewStatusDir = ensureDir(options.reviewStatusDir, 'review-status directory');
  const executionPackDir = ensureDir(options.executionPackDir, 'execution-pack directory');

  const batchSummaryPath = ensureFile(path.join(batchDir, 'summary.json'), 'batch summary');
  const referenceAuditSummaryPath = ensureFile(path.join(referenceAuditDir, 'summary.json'), 'reference-audit summary');
  const reviewedManifestPath = ensureFile(path.join(reviewedDir, 'reviewed-triage.json'), 'reviewed manifest');
  const reviewedSummaryPath = ensureFile(path.join(reviewedDir, 'summary.json'), 'reviewed summary');
  const reviewStatusSummaryPath = ensureFile(path.join(reviewStatusDir, 'summary.json'), 'review-status summary');
  const executionPackSummaryPath = ensureFile(path.join(executionPackDir, 'summary.json'), 'execution-pack summary');
  const approvedBranchesPath = ensureFile(path.join(executionPackDir, 'approved-remote-branches.json'), 'execution-pack approved branches');
  const dryRunReportPath = ensureFile(path.join(executionPackDir, 'branch-cleanup-dry-run-report.json'), 'execution-pack dry-run report');

  return {
    triageJsonPath,
    batchDir,
    referenceAuditDir,
    reviewedDir,
    reviewStatusDir,
    executionPackDir,
    batchSummaryPath,
    referenceAuditSummaryPath,
    reviewedManifestPath,
    reviewedSummaryPath,
    reviewStatusSummaryPath,
    executionPackSummaryPath,
    approvedBranchesPath,
    dryRunReportPath,
    applyReportPath: resolveIfExists(path.join(executionPackDir, 'branch-cleanup-apply-report.json')),
  };
};

const validateTriage = (artifacts) => {
  const triage = readJson(artifacts.triageJsonPath);
  const sourceInventory = ensureObject(triage?.sourceInventory, 'triage sourceInventory');
  const remoteMerged = ensureArray(triage?.remoteMerged, 'triage remoteMerged');
  const remoteStale = ensureArray(triage?.remoteStale, 'triage remoteStale');
  const summary = ensureObject(triage?.summary, 'triage summary');

  const inventoryPath = ensureFile(String(sourceInventory.path || ''), 'triage source inventory');
  assert(String(sourceInventory.generatedAt || '').trim(), 'triage sourceInventory.generatedAt is required');
  assert(String(sourceInventory.base || '').trim(), 'triage sourceInventory.base is required');
  assert(String(sourceInventory.remote || '').trim(), 'triage sourceInventory.remote is required');
  ensureInteger(Number(summary.remoteMergedCandidates), 'triage summary.remoteMergedCandidates');
  ensureInteger(Number(summary.remoteStaleCandidates), 'triage summary.remoteStaleCandidates');
  assert(Number(summary.remoteMergedCandidates) === remoteMerged.length, 'triage merged count mismatch');
  assert(Number(summary.remoteStaleCandidates) === remoteStale.length, 'triage stale count mismatch');

  return { triage, sourceInventory, inventoryPath, remoteMerged, remoteStale, summary };
};

const validateBatchSummary = (artifacts, triageState) => {
  const summary = readJson(artifacts.batchSummaryPath);
  const sourceTriage = ensureObject(summary?.sourceTriage, 'batch summary sourceTriage');
  resolveSamePath(sourceTriage.path, artifacts.triageJsonPath, 'batch summary sourceTriage.path');
  assert(String(sourceTriage.generatedAt || '') === String(triageState.triage.generatedAt || ''), 'batch summary sourceTriage.generatedAt mismatch');
  assert(String(sourceTriage.base || '') === String(triageState.sourceInventory.base || ''), 'batch summary sourceTriage.base mismatch');
  assert(String(sourceTriage.remote || '') === String(triageState.sourceInventory.remote || ''), 'batch summary sourceTriage.remote mismatch');

  const batchFiles = {
    batchA: 'batch-a-merged.json',
    batchB: 'batch-b-low-risk-stale.json',
    batchC: 'batch-c-ambiguous-stale.json',
  };
  const expectedCounts = {
    batchA: triageState.remoteMerged.length,
    batchB: countBatchB(triageState.remoteStale),
    batchC: countBatchC(triageState.remoteStale),
  };

  const payloads = {};
  for (const [key, filename] of Object.entries(batchFiles)) {
    const batchEntry = ensureObject(summary?.batches?.[key], `batch summary ${key}`);
    const batchPath = ensureFile(path.join(artifacts.batchDir, filename), `${key} payload`);
    resolveSamePath(batchEntry.jsonPath, batchPath, `${key} jsonPath`);
    const payload = readJson(batchPath);
    const items = ensureArray(payload?.items, `${key} items`);
    const payloadSourceTriage = ensureObject(payload?.sourceTriage, `${key} sourceTriage`);
    resolveSamePath(payloadSourceTriage.path, artifacts.triageJsonPath, `${key} sourceTriage.path`);
    assert(String(payloadSourceTriage.generatedAt || '') === String(triageState.triage.generatedAt || ''), `${key} sourceTriage.generatedAt mismatch`);
    assert(String(payloadSourceTriage.inventoryGeneratedAt || '') === String(triageState.sourceInventory.generatedAt || ''), `${key} sourceTriage.inventoryGeneratedAt mismatch`);
    assert(String(payloadSourceTriage.base || '') === String(triageState.sourceInventory.base || ''), `${key} sourceTriage.base mismatch`);
    assert(String(payloadSourceTriage.remote || '') === String(triageState.sourceInventory.remote || ''), `${key} sourceTriage.remote mismatch`);
    ensureInteger(Number(payload?.count), `${key} payload.count`);
    ensureInteger(Number(batchEntry.count), `${key} summary.count`);
    assert(Number(payload.count) === items.length, `${key} payload count does not match items length`);
    assert(Number(batchEntry.count) === Number(payload.count), `${key} summary count mismatch`);
    assert(Number(payload.count) === expectedCounts[key], `${key} count does not match triage selection`);
    payloads[key] = payload;
  }

  return {
    summary,
    payloads,
    counts: {
      batchA: expectedCounts.batchA,
      batchB: expectedCounts.batchB,
      batchC: expectedCounts.batchC,
    },
  };
};

const validateReferenceAudit = (artifacts, triageState, batchState) => {
  const summary = readJson(artifacts.referenceAuditSummaryPath);
  resolveSamePath(summary?.source?.batchDir, artifacts.batchDir, 'reference-audit summary.source.batchDir');

  const slugs = {
    batchA: 'batch-a-merged',
    batchB: 'batch-b-low-risk-stale',
    batchC: 'batch-c-ambiguous-stale',
  };
  const counts = {};

  for (const [key, slug] of Object.entries(slugs)) {
    const entry = ensureObject(summary?.batches?.[slug], `reference-audit summary ${slug}`);
    const jsonPath = ensureFile(path.join(artifacts.referenceAuditDir, `${slug}.audit.json`), `${slug} audit payload`);
    resolveSamePath(entry.jsonPath, jsonPath, `${slug} audit jsonPath`);
    const payload = readJson(jsonPath);
    const items = ensureArray(payload?.items, `${slug} audit items`);
    const payloadSourceTriage = ensureObject(payload?.sourceTriage, `${slug} audit sourceTriage`);
    resolveSamePath(payloadSourceTriage.path, artifacts.triageJsonPath, `${slug} audit sourceTriage.path`);
    assert(String(payloadSourceTriage.generatedAt || '') === String(triageState.triage.generatedAt || ''), `${slug} audit sourceTriage.generatedAt mismatch`);
    assert(String(payloadSourceTriage.inventoryGeneratedAt || '') === String(triageState.sourceInventory.generatedAt || ''), `${slug} audit sourceTriage.inventoryGeneratedAt mismatch`);
    assert(String(payloadSourceTriage.base || '') === String(triageState.sourceInventory.base || ''), `${slug} audit sourceTriage.base mismatch`);
    assert(String(payloadSourceTriage.remote || '') === String(triageState.sourceInventory.remote || ''), `${slug} audit sourceTriage.remote mismatch`);
    const payloadSummary = ensureObject(payload?.summary, `${slug} audit summary`);
    ensureInteger(Number(payloadSummary.total), `${slug} audit summary.total`);
    assert(Number(payloadSummary.total) === items.length, `${slug} audit total mismatch`);
    assert(Number(payloadSummary.total) === batchState.counts[key], `${slug} audit total does not match batch count`);
    assert(Number(entry?.summary?.total ?? -1) === Number(payloadSummary.total), `${slug} summary total mismatch`);
    counts[slug] = Number(payloadSummary.total);
  }

  return { summary, counts };
};

const validateReviewed = (artifacts, triageState, batchState) => {
  const reviewedManifest = readJson(artifacts.reviewedManifestPath);
  const reviewedSummary = readJson(artifacts.reviewedSummaryPath);
  const reviewedDecisions = ensureObject(reviewedManifest?.reviewedDecisions, 'reviewed manifest reviewedDecisions');

  resolveSamePath(reviewedSummary.reviewedManifestPath, artifacts.reviewedManifestPath, 'reviewed summary reviewedManifestPath');
  resolveSamePath(reviewedSummary.sourceTriagePath, artifacts.triageJsonPath, 'reviewed summary sourceTriagePath');
  resolveSamePath(reviewedSummary.sourceBatchDir, artifacts.batchDir, 'reviewed summary sourceBatchDir');
  resolveSamePath(reviewedDecisions.sourceTriagePath, artifacts.triageJsonPath, 'reviewed manifest sourceTriagePath');
  resolveSamePath(reviewedDecisions.sourceBatchDir, artifacts.batchDir, 'reviewed manifest sourceBatchDir');
  assert(String(reviewedManifest?.sourceInventory?.base || '') === String(triageState.sourceInventory.base || ''), 'reviewed manifest sourceInventory.base mismatch');
  assert(String(reviewedManifest?.sourceInventory?.remote || '') === String(triageState.sourceInventory.remote || ''), 'reviewed manifest sourceInventory.remote mismatch');
  resolveSamePath(reviewedManifest?.sourceInventory?.path, triageState.sourceInventory.path, 'reviewed manifest sourceInventory.path');
  assert(String(reviewedManifest?.sourceInventory?.generatedAt || '') === String(triageState.sourceInventory.generatedAt || ''), 'reviewed manifest sourceInventory.generatedAt mismatch');

  const sourceBatches = ensureArray(reviewedDecisions.sourceBatches, 'reviewed manifest sourceBatches');
  const expectedBatchNames = [
    path.basename(batchState.summary.batches.batchB.jsonPath),
    path.basename(batchState.summary.batches.batchC.jsonPath),
  ].sort();
  assert(JSON.stringify([...sourceBatches].sort()) === JSON.stringify(expectedBatchNames), 'reviewed manifest sourceBatches mismatch');

  const summaryByBatch = ensureObject(reviewedSummary.summaryByBatch, 'reviewed summary summaryByBatch');
  assert(JSON.stringify(summaryByBatch) === JSON.stringify(reviewedDecisions.summaryByBatch), 'reviewed summary summaryByBatch mismatch');
  const appliedRows = ensureArray(reviewedSummary.appliedRows, 'reviewed summary appliedRows');
  const totalApplied = Object.values(summaryByBatch).reduce((sum, item) => sum + Number(item?.total || 0), 0);
  assert(totalApplied === appliedRows.length, 'reviewed summary appliedRows count mismatch');

  return { reviewedManifest, reviewedSummary, appliedRowsCount: appliedRows.length };
};

const validateReviewStatus = (artifacts, reviewedState, referenceAuditState) => {
  const summary = readJson(artifacts.reviewStatusSummaryPath);
  resolveSamePath(summary?.source?.reviewedManifestPath, artifacts.reviewedManifestPath, 'review-status source.reviewedManifestPath');
  resolveSamePath(summary?.source?.referenceAuditDir, artifacts.referenceAuditDir, 'review-status source.referenceAuditDir');
  resolveSamePath(summary?.source?.sourceTriagePath, reviewedState.reviewedManifest.reviewedDecisions.sourceTriagePath, 'review-status source.sourceTriagePath');

  if (summary?.mergedAudit) {
    assert(Number(summary.mergedAudit.total) === Number(referenceAuditState.summary?.batches?.['batch-a-merged']?.summary?.total || 0), 'review-status mergedAudit.total mismatch');
    assert(Number(summary.mergedAudit.clearCandidates) === Number(referenceAuditState.summary?.batches?.['batch-a-merged']?.summary?.clearCandidates || 0), 'review-status mergedAudit.clearCandidates mismatch');
  }

  const fileCounts = {};
  for (const statusName of REVIEW_STATUS_FILES) {
    const payload = readJson(ensureFile(path.join(artifacts.reviewStatusDir, `${statusName}.json`), `${statusName}.json`));
    fileCounts[statusName] = ensureArray(payload, `${statusName}.json`).length;
  }
  const deleteReadyBranchesPayload = readJson(ensureFile(path.join(artifacts.reviewStatusDir, 'delete-ready.branches.json'), 'delete-ready.branches.json'));
  const deleteReadyBranchEntries = ensureArray(deleteReadyBranchesPayload?.branches, 'delete-ready.branches.json branches');
  assert(deleteReadyBranchEntries.length === fileCounts['delete-ready'], 'delete-ready branch list count mismatch');

  const overall = ensureObject(summary?.overall, 'review-status overall');
  assert(Number(overall['delete-ready']) === fileCounts['delete-ready'], 'review-status delete-ready mismatch');
  assert(Number(overall['delete-blocked']) === fileCounts['delete-blocked'], 'review-status delete-blocked mismatch');
  assert(Number(overall.retained) === fileCounts.retained, 'review-status retained mismatch');
  assert(Number(overall['pending-review']) === fileCounts['pending-review'], 'review-status pending-review mismatch');
  assert(Number(overall['missing-audit']) === fileCounts['missing-audit'], 'review-status missing-audit mismatch');

  return { summary, deleteReadyBranchEntries, overall };
};

const validateExecutionPack = (artifacts, triageState, reviewStatusState) => {
  const summary = readJson(artifacts.executionPackSummaryPath);
  const approvedBranchList = readJson(artifacts.approvedBranchesPath);
  const dryRunReport = readJson(artifacts.dryRunReportPath);

  resolveSamePath(summary?.source?.reviewStatusDir, artifacts.reviewStatusDir, 'execution-pack source.reviewStatusDir');
  resolveSamePath(summary?.source?.reviewedManifestPath, artifacts.reviewedManifestPath, 'execution-pack source.reviewedManifestPath');
  resolveSamePath(summary?.source?.sourceTriagePath, artifacts.triageJsonPath, 'execution-pack source.sourceTriagePath');
  resolveSamePath(summary?.artifacts?.approvedBranchListPath, artifacts.approvedBranchesPath, 'execution-pack approvedBranchListPath');
  resolveSamePath(summary?.artifacts?.dryRunReportPath, artifacts.dryRunReportPath, 'execution-pack dryRunReportPath');
  resolveSamePath(summary?.artifacts?.commandsPath, path.join(artifacts.executionPackDir, 'commands.sh'), 'execution-pack commandsPath');
  resolveSamePath(summary?.artifacts?.applyCommandPath, path.join(artifacts.executionPackDir, 'apply-command.txt'), 'execution-pack applyCommandPath');
  resolveSamePath(summary?.sourceInventory?.path, triageState.sourceInventory.path, 'execution-pack summary sourceInventory.path');
  assert(String(summary?.sourceInventory?.generatedAt || '') === String(triageState.sourceInventory.generatedAt || ''), 'execution-pack summary sourceInventory.generatedAt mismatch');
  assert(String(summary?.sourceInventory?.base || '') === String(triageState.sourceInventory.base || ''), 'execution-pack summary sourceInventory.base mismatch');
  assert(String(summary?.sourceInventory?.remote || '') === String(triageState.sourceInventory.remote || ''), 'execution-pack summary sourceInventory.remote mismatch');

  const approvedBranches = ensureArray(approvedBranchList?.branches, 'execution-pack approved branches');
  resolveSamePath(approvedBranchList?.sourceReviewStatus?.dir, artifacts.reviewStatusDir, 'approved branches sourceReviewStatus.dir');
  resolveSamePath(approvedBranchList?.sourceReviewStatus?.summaryPath, artifacts.reviewStatusSummaryPath, 'approved branches sourceReviewStatus.summaryPath');
  resolveSamePath(approvedBranchList?.sourceReviewStatus?.reviewedManifestPath, artifacts.reviewedManifestPath, 'approved branches reviewedManifestPath');
  resolveSamePath(approvedBranchList?.sourceReviewStatus?.referenceAuditDir, artifacts.referenceAuditDir, 'approved branches referenceAuditDir');
  resolveSamePath(approvedBranchList?.sourceReviewStatus?.sourceTriagePath, artifacts.triageJsonPath, 'approved branches sourceTriagePath');
  resolveSamePath(approvedBranchList?.sourceInventory?.path, triageState.sourceInventory.path, 'approved branches sourceInventory.path');
  assert(String(approvedBranchList?.sourceInventory?.generatedAt || '') === String(triageState.sourceInventory.generatedAt || ''), 'approved branches sourceInventory.generatedAt mismatch');
  assert(String(approvedBranchList?.sourceInventory?.base || '') === String(triageState.sourceInventory.base || ''), 'approved branches sourceInventory.base mismatch');
  assert(String(approvedBranchList?.sourceInventory?.remote || '') === String(triageState.sourceInventory.remote || ''), 'approved branches sourceInventory.remote mismatch');

  assert(Number(summary?.deleteReady?.count ?? -1) === approvedBranches.length, 'execution-pack deleteReady count mismatch');
  assert(approvedBranches.length === reviewStatusState.deleteReadyBranchEntries.length, 'execution-pack approved branch count mismatch');
  const dryRunSelection = ensureObject(dryRunReport?.remote?.selection, 'execution-pack dry-run selection');
  assert(String(dryRunSelection.mode || '') === 'branch-list', 'execution-pack dry-run selection.mode mismatch');
  resolveSamePath(dryRunSelection.sourcePath, artifacts.approvedBranchesPath, 'execution-pack dry-run selection.sourcePath');
  assert(String(dryRunSelection.expectedBase || '') === '', 'execution-pack dry-run expectedBase should be empty for branch-list mode');
  assert(String(dryRunSelection.expectedRemote || '') === '', 'execution-pack dry-run expectedRemote should be empty for branch-list mode');
  assert(Number(dryRunReport?.remote?.totalCandidates ?? -1) === approvedBranches.length, 'execution-pack dry-run totalCandidates mismatch');
  const plannedDetailed = ensureArray(dryRunReport?.remote?.plannedDetailed, 'execution-pack dry-run plannedDetailed');
  const blocked = ensureArray(dryRunReport?.remote?.blocked, 'execution-pack dry-run blocked');
  assert(plannedDetailed.length + blocked.length === approvedBranches.length, 'execution-pack dry-run planned+blocked mismatch');
  assert(Number(summary?.dryRun?.planned ?? -1) === plannedDetailed.length, 'execution-pack dry-run planned count mismatch');
  assert(Number(summary?.dryRun?.blocked ?? -1) === blocked.length, 'execution-pack dry-run blocked count mismatch');

  return { summary, approvedBranches, dryRunReport };
};

const validatePostApply = (artifacts, executionState) => {
  const summaryPath = artifacts.postVerifySummaryPath;
  if (!summaryPath) {
    return { available: false, counts: null };
  }
  const summary = readJson(summaryPath);
  const cleanupReportPath = ensureFile(summary?.source?.cleanupReportPath, 'post-apply cleanup report');
  const cleanupReport = readJson(cleanupReportPath);

  if (artifacts.applyReportPath) {
    resolveSamePath(cleanupReportPath, artifacts.applyReportPath, 'post-apply cleanup report path');
  }

  assert(String(summary?.remoteName || '') === String(cleanupReport?.remoteName || ''), 'post-apply remoteName mismatch');
  assert(String(summary?.scope || '') === String(cleanupReport?.scope || ''), 'post-apply scope mismatch');

  const deleted = ensureArray(summary?.deleted, 'post-apply deleted');
  const failedDeletes = ensureArray(summary?.failedDeletes, 'post-apply failedDeletes');
  const blocked = ensureArray(summary?.blocked, 'post-apply blocked');
  const plannedButNotDeleted = ensureArray(summary?.plannedButNotDeleted, 'post-apply plannedButNotDeleted');
  const counts = ensureObject(summary?.counts, 'post-apply counts');
  assert(Number(counts.reportedDeleted) === deleted.length, 'post-apply reportedDeleted mismatch');
  assert(Number(counts.failedDeletes) === failedDeletes.length, 'post-apply failedDeletes count mismatch');
  assert(Number(counts.blocked) === blocked.length, 'post-apply blocked count mismatch');
  assert(Number(counts.plannedButNotDeleted) === plannedButNotDeleted.length, 'post-apply plannedButNotDeleted count mismatch');
  assert(Number(counts.presentOnRemote) === Number(counts.stillPresent) + Number(counts.recreatedRefs), 'post-apply presentOnRemote mismatch');
  assert(Number(counts.verifiedAbsent) + Number(counts.presentOnRemote) === deleted.length, 'post-apply verifiedAbsent+presentOnRemote mismatch');

  const applyDeleted = ensureArray(cleanupReport?.remote?.deleted, 'cleanup report remote.deleted');
  const applyFailed = ensureArray(cleanupReport?.remote?.failed, 'cleanup report remote.failed');
  const applyBlocked = ensureArray(cleanupReport?.remote?.blocked, 'cleanup report remote.blocked');
  const applyPlannedDetailed = ensureArray(cleanupReport?.remote?.plannedDetailed, 'cleanup report remote.plannedDetailed');
  assert(applyDeleted.length === deleted.length, 'cleanup report deleted count mismatch with post-apply summary');
  assert(applyFailed.length === failedDeletes.length, 'cleanup report failed count mismatch with post-apply summary');
  assert(applyBlocked.length === blocked.length, 'cleanup report blocked count mismatch with post-apply summary');
  assert(applyPlannedDetailed.length === deleted.length + failedDeletes.length + plannedButNotDeleted.length, 'cleanup report plannedDetailed mismatch with post-apply summary');

  if (executionState.approvedBranches.length) {
    assert(applyPlannedDetailed.length <= executionState.approvedBranches.length, 'post-apply plannedDetailed exceeds approved branch count');
  }

  return { available: true, summary, cleanupReport };
};

const validateRefreshAudit = (artifacts, triageState, postApplyState) => {
  if (!artifacts.refreshAuditSummaryPath) {
    return { available: false, counts: null };
  }
  assert(postApplyState.available, 'refresh-audit summary requires post-apply verify summary');
  const summary = readJson(artifacts.refreshAuditSummaryPath);
  resolveSamePath(summary?.source?.postVerifySummaryPath, artifacts.postVerifySummaryPath, 'refresh-audit source.postVerifySummaryPath');
  const refreshedTriagePath = ensureFile(summary?.source?.refreshedTriagePath, 'refresh-audit refreshed triage');
  const refreshedTriage = readJson(refreshedTriagePath);
  const refreshedSourceInventory = ensureObject(refreshedTriage?.sourceInventory, 'refresh-audit refreshed triage sourceInventory');
  assert(String(refreshedSourceInventory.base || '') === String(triageState.sourceInventory.base || ''), 'refresh-audit refreshed triage base mismatch');
  assert(String(refreshedSourceInventory.remote || '') === String(triageState.sourceInventory.remote || ''), 'refresh-audit refreshed triage remote mismatch');
  const refreshedMerged = ensureArray(refreshedTriage?.remoteMerged, 'refresh-audit refreshed triage remoteMerged');
  const refreshedStale = ensureArray(refreshedTriage?.remoteStale, 'refresh-audit refreshed triage remoteStale');
  const counts = ensureObject(summary?.counts, 'refresh-audit counts');
  const audit = ensureArray(summary?.audit, 'refresh-audit audit');
  const recreated = ensureArray(summary?.recreated || [], 'refresh-audit recreated');
  const verifiedAbsentCount = countStatus(postApplyState.summary.deleted, 'verified-absent');
  const recreatedCount = countStatus(postApplyState.summary.deleted, 'recreated-ref');
  assert(Number(counts.verifiedAbsentInput) === verifiedAbsentCount, 'refresh-audit verifiedAbsentInput mismatch');
  assert(Number(counts.confirmedRemoved) + Number(counts.reappearedInTriage) === Number(counts.verifiedAbsentInput), 'refresh-audit confirmed+reappeared mismatch');
  assert(Number(counts.recreatedRefInput) === recreatedCount, 'refresh-audit recreatedRefInput mismatch');
  assert(Number(counts.recreatedRefInTriage) + Number(counts.recreatedRefOutsideTriage) === Number(counts.recreatedRefInput), 'refresh-audit recreated counts mismatch');
  assert(Number(counts.refreshedRemoteMerged) === refreshedMerged.length, 'refresh-audit refreshedRemoteMerged mismatch');
  assert(Number(counts.refreshedRemoteStale) === refreshedStale.length, 'refresh-audit refreshedRemoteStale mismatch');
  assert(audit.length === Number(counts.verifiedAbsentInput), 'refresh-audit audit row count mismatch');
  assert(recreated.length === Number(counts.recreatedRefInput), 'refresh-audit recreated row count mismatch');

  return { available: true, summary, refreshedTriagePath };
};

const renderSummaryMarkdown = (summary) => {
  const rows = [
    ['triage merged/stale', `${summary.counts.triage.remoteMerged} / ${summary.counts.triage.remoteStale}`],
    ['batches A/B/C', `${summary.counts.batches.A} / ${summary.counts.batches.B} / ${summary.counts.batches.C}`],
    ['review-status ready/blocked/pending', `${summary.counts.reviewStatus['delete-ready']} / ${summary.counts.reviewStatus['delete-blocked']} / ${summary.counts.reviewStatus['pending-review']}`],
    ['execution-pack approved/planned/blocked', `${summary.counts.executionPack.approvedBranches} / ${summary.counts.executionPack.dryRunPlanned} / ${summary.counts.executionPack.dryRunBlocked}`],
    ['post-apply available', summary.optional.postApplyVerify.available ? 'yes' : 'no'],
    ['refresh-audit available', summary.optional.refreshAudit.available ? 'yes' : 'no'],
  ];

  if (summary.optional.postApplyVerify.available) {
    rows.push([
      'post-apply deleted/verified/still-present',
      `${summary.optional.postApplyVerify.counts.reportedDeleted} / ${summary.optional.postApplyVerify.counts.verifiedAbsent} / ${summary.optional.postApplyVerify.counts.presentOnRemote}`,
    ]);
  }
  if (summary.optional.refreshAudit.available) {
    rows.push([
      'refresh confirmed/reappeared/recreated',
      `${summary.optional.refreshAudit.counts.confirmedRemoved} / ${summary.optional.refreshAudit.counts.reappearedInTriage} / ${summary.optional.refreshAudit.counts.recreatedRefInput}`,
    ]);
  }

  return `# Remote Cleanup Artifact Consistency Check

- generatedAt: ${summary.generatedAt}
- triage: \`${summary.source.triageJsonPath}\`
- execution pack: \`${summary.source.executionPackDir}\`
- status: all consistency checks passed

${renderTable(['metric', 'value'], rows)}`;
};

const renderIssueComment = (summary) => {
  const lines = [
    `Artifact consistency check from \`${summary.source.triageJsonPath}\`:`,
    `- triage merged/stale: ${summary.counts.triage.remoteMerged}/${summary.counts.triage.remoteStale}`,
    `- batches A/B/C: ${summary.counts.batches.A}/${summary.counts.batches.B}/${summary.counts.batches.C}`,
    `- delete-ready/blocked/pending: ${summary.counts.reviewStatus['delete-ready']}/${summary.counts.reviewStatus['delete-blocked']}/${summary.counts.reviewStatus['pending-review']}`,
    `- execution-pack approved/planned/blocked: ${summary.counts.executionPack.approvedBranches}/${summary.counts.executionPack.dryRunPlanned}/${summary.counts.executionPack.dryRunBlocked}`,
    `- post-apply verify: ${summary.optional.postApplyVerify.available ? 'validated' : 'not provided'}`,
    `- refresh-audit: ${summary.optional.refreshAudit.available ? 'validated' : 'not provided'}`,
  ];
  if (summary.optional.postApplyVerify.available) {
    lines.push(
      `- deleted/verified/present-on-remote: ${summary.optional.postApplyVerify.counts.reportedDeleted}/${summary.optional.postApplyVerify.counts.verifiedAbsent}/${summary.optional.postApplyVerify.counts.presentOnRemote}`,
    );
  }
  if (summary.optional.refreshAudit.available) {
    lines.push(
      `- refresh confirmed/reappeared/recreated: ${summary.optional.refreshAudit.counts.confirmedRemoved}/${summary.optional.refreshAudit.counts.reappearedInTriage}/${summary.optional.refreshAudit.counts.recreatedRefInput}`,
    );
  }
  return `${lines.join('\n')}\n`;
};

const writeFile = (targetPath, content) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
};

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const outputDir = path.resolve(options.outputDir);
  const artifacts = loadCoreArtifacts({
    ...options,
    outputDir,
  });
  artifacts.postVerifySummaryPath = resolveIfExists(options.postVerifySummaryJson);
  artifacts.refreshAuditSummaryPath = resolveIfExists(options.refreshAuditSummaryJson);

  const triageState = validateTriage(artifacts);
  const batchState = validateBatchSummary(artifacts, triageState);
  const referenceAuditState = validateReferenceAudit(artifacts, triageState, batchState);
  const reviewedState = validateReviewed(artifacts, triageState, batchState);
  const reviewStatusState = validateReviewStatus(artifacts, reviewedState, referenceAuditState);
  const executionState = validateExecutionPack(artifacts, triageState, reviewStatusState);
  const postApplyState = validatePostApply(artifacts, executionState);
  const refreshAuditState = validateRefreshAudit(artifacts, triageState, postApplyState);

  const summary = {
    generatedAt: new Date().toISOString(),
    source: {
      triageJsonPath: artifacts.triageJsonPath,
      batchDir: artifacts.batchDir,
      referenceAuditDir: artifacts.referenceAuditDir,
      reviewedDir: artifacts.reviewedDir,
      reviewStatusDir: artifacts.reviewStatusDir,
      executionPackDir: artifacts.executionPackDir,
      postVerifySummaryPath: artifacts.postVerifySummaryPath || '',
      refreshAuditSummaryPath: artifacts.refreshAuditSummaryPath || '',
    },
    sourceInventory: {
      path: triageState.sourceInventory.path,
      generatedAt: triageState.sourceInventory.generatedAt,
      base: triageState.sourceInventory.base,
      remote: triageState.sourceInventory.remote,
    },
    counts: {
      triage: {
        remoteMerged: triageState.remoteMerged.length,
        remoteStale: triageState.remoteStale.length,
      },
      batches: {
        A: batchState.counts.batchA,
        B: batchState.counts.batchB,
        C: batchState.counts.batchC,
      },
      referenceAudit: {
        A: referenceAuditState.counts['batch-a-merged'],
        B: referenceAuditState.counts['batch-b-low-risk-stale'],
        C: referenceAuditState.counts['batch-c-ambiguous-stale'],
      },
      reviewed: {
        appliedRows: reviewedState.appliedRowsCount,
      },
      reviewStatus: reviewStatusState.overall,
      executionPack: {
        approvedBranches: executionState.approvedBranches.length,
        dryRunPlanned: executionState.dryRunReport.remote.plannedDetailed.length,
        dryRunBlocked: executionState.dryRunReport.remote.blocked.length,
      },
    },
    optional: {
      postApplyVerify: postApplyState.available
        ? {
            available: true,
            counts: postApplyState.summary.counts,
          }
        : {
            available: false,
            counts: null,
          },
      refreshAudit: refreshAuditState.available
        ? {
            available: true,
            counts: refreshAuditState.summary.counts,
            refreshedTriagePath: refreshAuditState.refreshedTriagePath,
          }
        : {
            available: false,
            counts: null,
            refreshedTriagePath: '',
          },
    },
  };

  writeFile(path.join(outputDir, 'summary.json'), `${JSON.stringify(summary, null, 2)}\n`);
  writeFile(path.join(outputDir, 'summary.md'), `${renderSummaryMarkdown(summary)}\n`);
  writeFile(path.join(outputDir, 'issue-comment.md'), renderIssueComment(summary));

  console.log(`[remote-cleanup-artifact-consistency-check] wrote ${path.join(outputDir, 'summary.json')}`);
  console.log(
    `[remote-cleanup-artifact-consistency-check] deleteReady=${summary.counts.reviewStatus['delete-ready']} planned=${summary.counts.executionPack.dryRunPlanned} postApply=${summary.optional.postApplyVerify.available ? 'yes' : 'no'} refresh=${summary.optional.refreshAudit.available ? 'yes' : 'no'}`,
  );
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error('[remote-cleanup-artifact-consistency-check] ERROR:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}
