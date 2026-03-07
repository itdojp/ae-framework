#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { LOW_RISK_PREFIXES, renderTable } from './remote-branch-triage.mjs';

const DEFAULT_INPUT_JSON = 'tmp/maintenance/remote-branch-triage.json';
const DEFAULT_BATCH_DIR = 'tmp/maintenance/remote-cleanup-batches';
const DEFAULT_OUTPUT_DIR = 'tmp/maintenance/remote-cleanup-reviewed';
const DECISION_VALUES = new Set(['', 'keep', 'archive', 'delete']);
const REVIEW_BATCHES = [
  { id: 'B', filename: 'batch-b-low-risk-stale.json', title: 'Low-risk stale branches' },
  { id: 'C', filename: 'batch-c-ambiguous-stale.json', title: 'Ambiguous stale branches' },
];

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-cleanup-decision-sync.mjs [options]

Options:
  --input-json <path>   Source remote-branch-triage JSON (default: ${DEFAULT_INPUT_JSON})
  --batch-dir <path>    Directory containing reviewed batch JSON files (default: ${DEFAULT_BATCH_DIR})
  --output-dir <path>   Output directory for reviewed manifest and summaries (default: ${DEFAULT_OUTPUT_DIR})
  --help                Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    inputJson: DEFAULT_INPUT_JSON,
    batchDir: DEFAULT_BATCH_DIR,
    outputDir: DEFAULT_OUTPUT_DIR,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--input-json') {
      options.inputJson = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--batch-dir') {
      options.batchDir = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = String(argv[++i] || '').trim();
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.inputJson) throw new Error('--input-json is required');
  if (!options.batchDir) throw new Error('--batch-dir is required');
  if (!options.outputDir) throw new Error('--output-dir is required');
  return options;
};

const readJson = (targetPath) => JSON.parse(fs.readFileSync(targetPath, 'utf8'));

const writeFile = (targetPath, content) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
};

const startsWithLowRiskPrefix = (branch) => LOW_RISK_PREFIXES.some((prefix) => branch.startsWith(prefix));

const validateBatchProvenance = (payload, report, inputJsonPath, filename) => {
  const sourceTriage = payload?.sourceTriage || {};
  const reportSource = report?.sourceInventory || {};
  if (String(sourceTriage.path || '') !== inputJsonPath) {
    throw new Error(`${filename} sourceTriage.path does not match input-json`);
  }
  if (String(sourceTriage.generatedAt || '') !== String(report.generatedAt || '')) {
    throw new Error(`${filename} sourceTriage.generatedAt does not match source triage`);
  }
  if (String(sourceTriage.inventoryGeneratedAt || '') !== String(reportSource.generatedAt || '')) {
    throw new Error(`${filename} sourceTriage.inventoryGeneratedAt does not match source inventory`);
  }
  if (String(sourceTriage.base || '') !== String(reportSource.base || '')) {
    throw new Error(`${filename} sourceTriage.base does not match source inventory base`);
  }
  if (String(sourceTriage.remote || '') !== String(reportSource.remote || '')) {
    throw new Error(`${filename} sourceTriage.remote does not match source inventory remote`);
  }
};

const loadReviewedBatches = (batchDir, report, inputJsonPath) => {
  const items = [];
  const seenBranches = new Set();
  for (const batch of REVIEW_BATCHES) {
    const targetPath = path.join(batchDir, batch.filename);
    if (!fs.existsSync(targetPath)) continue;
    const payload = readJson(targetPath);
    validateBatchProvenance(payload, report, inputJsonPath, batch.filename);
    const batchItems = Array.isArray(payload?.items) ? payload.items : [];
    for (const item of batchItems) {
      const branch = String(item?.branch || '').trim();
      if (!branch) {
        throw new Error(`${batch.filename} contains an item without branch`);
      }
      if (seenBranches.has(branch)) {
        throw new Error(`${batch.filename} contains duplicate reviewed branch row: ${branch}`);
      }
      seenBranches.add(branch);
      const decision = typeof item?.decision === 'string' ? item.decision.trim() : '';
      if (!DECISION_VALUES.has(decision)) {
        throw new Error(`${batch.filename} contains unsupported decision for ${branch}: ${decision}`);
      }
      items.push({
        batchId: batch.id,
        batchTitle: batch.title,
        sourcePath: targetPath,
        branch,
        branchOid: typeof item?.branchOid === 'string' ? item.branchOid.trim() : '',
        decision,
        notes: typeof item?.notes === 'string' ? item.notes : '',
      });
    }
  }
  if (items.length === 0) {
    throw new Error(`No reviewed batch rows found under ${batchDir}`);
  }
  return items;
};

const buildStaleIndex = (report) => {
  const remoteStale = Array.isArray(report?.remoteStale) ? report.remoteStale : [];
  const index = new Map();
  for (const item of remoteStale) {
    const branch = String(item?.branch || '').trim();
    if (!branch) continue;
    if (index.has(branch)) {
      throw new Error(`remoteStale contains duplicate branch entries: ${branch}`);
    }
    index.set(branch, item);
  }
  return index;
};

const mergeReviewedDecisions = (report, reviewedItems) => {
  const staleIndex = buildStaleIndex(report);
  const lookupCoverage = String(report?.githubPullRequests?.lookupCoverage || '');
  const summaryByBatch = Object.fromEntries(
    REVIEW_BATCHES.map((batch) => [
      batch.id,
      {
        id: batch.id,
        title: batch.title,
        total: 0,
        keep: 0,
        archive: 0,
        delete: 0,
        pending: 0,
        updated: 0,
        unchanged: 0,
      },
    ]),
  );

  const appliedRows = [];

  for (const reviewed of reviewedItems) {
    const target = staleIndex.get(reviewed.branch);
    if (!target) {
      throw new Error(`Reviewed batch row does not exist in remoteStale: ${reviewed.branch}`);
    }
    if (reviewed.branchOid && target.branchOid && reviewed.branchOid !== target.branchOid) {
      throw new Error(
        `Reviewed batch row branchOid mismatch for ${reviewed.branch}: ${reviewed.branchOid} != ${target.branchOid}`,
      );
    }
    if (reviewed.batchId === 'B' && (!startsWithLowRiskPrefix(reviewed.branch) || target.prState === 'ambiguous')) {
      throw new Error(`Batch B row no longer matches low-risk stale criteria: ${reviewed.branch}`);
    }
    if (reviewed.batchId === 'C' && target.prState !== 'ambiguous') {
      throw new Error(`Batch C row no longer matches ambiguous stale criteria: ${reviewed.branch}`);
    }
    if (reviewed.batchId === 'C' && reviewed.decision === 'delete' && !reviewed.notes.trim()) {
      throw new Error(`Batch C delete requires notes for ${reviewed.branch}`);
    }
    if (reviewed.decision === 'delete' && lookupCoverage === 'truncated' && target.prState === 'none') {
      throw new Error(`Cannot sync delete for ${reviewed.branch} while PR lookup coverage is truncated and prState=none`);
    }

    const bucket = summaryByBatch[reviewed.batchId];
    bucket.total += 1;
    bucket[reviewed.decision || 'pending'] += 1;

    const nextDecision = reviewed.decision;
    const nextNotes = reviewed.notes;
    const changed = target.decision !== nextDecision || target.notes !== nextNotes;
    if (changed) {
      target.decision = nextDecision;
      target.notes = nextNotes;
      bucket.updated += 1;
    } else {
      bucket.unchanged += 1;
    }

    appliedRows.push({
      batchId: reviewed.batchId,
      branch: reviewed.branch,
      decision: nextDecision || 'pending',
      notes: nextNotes,
      changed,
      branchOid: target.branchOid || reviewed.branchOid || '',
      prState: target.prState || '',
      riskBand: target.riskBand || '',
    });
  }

  return {
    report,
    summaryByBatch,
    appliedRows,
  };
};

const buildReviewMetadata = ({ inputJsonPath, batchDir, reviewedItems, summaryByBatch }) => ({
  generatedAt: new Date().toISOString(),
  sourceTriagePath: inputJsonPath,
  sourceBatchDir: batchDir,
  sourceBatches: Array.from(new Set(reviewedItems.map((item) => path.basename(item.sourcePath)))),
  summaryByBatch,
});

const renderSummaryMarkdown = (result, reviewedManifestPath) => {
  const rows = Object.values(result.reviewedDecisions.summaryByBatch).map((item) => [
    item.id,
    item.title,
    String(item.total),
    String(item.keep),
    String(item.archive),
    String(item.delete),
    String(item.pending),
    String(item.updated),
    String(item.unchanged),
  ]);

  return `# Remote Cleanup Decision Sync

- generatedAt: ${result.reviewedDecisions.generatedAt}
- source triage: \`${result.reviewedDecisions.sourceTriagePath}\`
- source batch dir: \`${result.reviewedDecisions.sourceBatchDir}\`
- reviewed manifest: \`${reviewedManifestPath}\`

${renderTable(['batch', 'title', 'total', 'keep', 'archive', 'delete', 'pending', 'updated', 'unchanged'], rows)}
`;
};

const renderIssueComment = (result, reviewedManifestPath) => {
  const lines = Object.values(result.reviewedDecisions.summaryByBatch).map(
    (item) =>
      `- Batch ${item.id}: total=${item.total}, keep=${item.keep}, archive=${item.archive}, delete=${item.delete}, pending=${item.pending}, updated=${item.updated}, unchanged=${item.unchanged}`,
  );

  return `Reviewed decision sync from \`${result.reviewedDecisions.sourceBatchDir}\`:
${lines.join('\n')}

Output manifest:
- \`${reviewedManifestPath}\`

Notes:
- this step only records reviewed decisions back into a derived triage manifest
- no remote delete was executed
- \`branch-cleanup.mjs --remote-manifest-mode stale-delete\` should use the reviewed manifest only after operator approval
`;
};

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const inputJsonPath = path.resolve(options.inputJson);
  const batchDir = path.resolve(options.batchDir);
  const outputDir = path.resolve(options.outputDir);
  const reviewedManifestPath = path.join(outputDir, 'reviewed-triage.json');
  const summaryJsonPath = path.join(outputDir, 'summary.json');
  const summaryMdPath = path.join(outputDir, 'summary.md');
  const issueCommentPath = path.join(outputDir, 'issue-comment.md');

  const report = readJson(inputJsonPath);
  const reviewedItems = loadReviewedBatches(batchDir, report, inputJsonPath);
  const merged = mergeReviewedDecisions(report, reviewedItems);
  merged.report.reviewedDecisions = buildReviewMetadata({
    inputJsonPath,
    batchDir,
    reviewedItems,
    summaryByBatch: merged.summaryByBatch,
  });

  writeFile(reviewedManifestPath, `${JSON.stringify(merged.report, null, 2)}\n`);
  writeFile(
    summaryJsonPath,
    `${JSON.stringify(
      {
        generatedAt: merged.report.reviewedDecisions.generatedAt,
        sourceTriagePath: inputJsonPath,
        sourceBatchDir: batchDir,
        reviewedManifestPath,
        summaryByBatch: merged.summaryByBatch,
        appliedRows: merged.appliedRows,
      },
      null,
      2,
    )}\n`,
  );
  writeFile(summaryMdPath, renderSummaryMarkdown(merged.report, reviewedManifestPath));
  writeFile(issueCommentPath, renderIssueComment(merged.report, reviewedManifestPath));

  console.log(`[remote-cleanup-decision-sync] wrote ${reviewedManifestPath}`);
  console.log(`[remote-cleanup-decision-sync] wrote ${summaryJsonPath}`);
  console.log(`[remote-cleanup-decision-sync] batches=${Object.keys(merged.summaryByBatch).length} rows=${merged.appliedRows.length}`);
};

const currentFilePath = fileURLToPath(import.meta.url);
if (process.argv[1] && path.resolve(process.argv[1]) === currentFilePath) {
  try {
    run();
  } catch (error) {
    console.error('[remote-cleanup-decision-sync] ERROR:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}
