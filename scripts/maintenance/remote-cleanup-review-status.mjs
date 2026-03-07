#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { LOW_RISK_PREFIXES, renderTable } from './remote-branch-triage.mjs';

const DEFAULT_REVIEWED_MANIFEST_JSON = 'tmp/maintenance/remote-cleanup-reviewed/reviewed-triage.json';
const DEFAULT_REFERENCE_AUDIT_DIR = 'tmp/maintenance/remote-cleanup-reference-audit';
const DEFAULT_OUTPUT_DIR = 'tmp/maintenance/remote-cleanup-review-status';
const AUDIT_FILENAMES = [
  'batch-a-merged.audit.json',
  'batch-b-low-risk-stale.audit.json',
  'batch-c-ambiguous-stale.audit.json',
];
const STATUS_ORDER = ['delete-ready', 'delete-blocked', 'retained', 'pending-review', 'missing-audit'];

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-cleanup-review-status.mjs [options]

Options:
  --reviewed-manifest-json <path>  Reviewed triage manifest path (default: ${DEFAULT_REVIEWED_MANIFEST_JSON})
  --reference-audit-dir <path>     Directory containing *.audit.json files (default: ${DEFAULT_REFERENCE_AUDIT_DIR})
  --output-dir <path>              Output directory for review status artifacts (default: ${DEFAULT_OUTPUT_DIR})
  --help                           Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    reviewedManifestJson: DEFAULT_REVIEWED_MANIFEST_JSON,
    referenceAuditDir: DEFAULT_REFERENCE_AUDIT_DIR,
    outputDir: DEFAULT_OUTPUT_DIR,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--reviewed-manifest-json') {
      options.reviewedManifestJson = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--reference-audit-dir') {
      options.referenceAuditDir = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = String(argv[++index] || '').trim();
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.reviewedManifestJson) throw new Error('--reviewed-manifest-json is required');
  if (!options.referenceAuditDir) throw new Error('--reference-audit-dir is required');
  if (!options.outputDir) throw new Error('--output-dir is required');
  return options;
};

const readJson = (targetPath) => JSON.parse(fs.readFileSync(targetPath, 'utf8'));

const writeFile = (targetPath, content) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
};

const startsWithLowRiskPrefix = (branch) => LOW_RISK_PREFIXES.some((prefix) => branch.startsWith(prefix));

const classifyBatchId = (item) => {
  if (item.prState === 'ambiguous') return 'C';
  if (startsWithLowRiskPrefix(String(item.branch || ''))) return 'B';
  return '';
};

const normalizeAuditItems = (payload) =>
  (Array.isArray(payload?.items) ? payload.items : []).map((item) => ({
    branch: String(item?.branch || '').trim(),
    branchOid: typeof item?.branchOid === 'string' ? item.branchOid.trim() : '',
    reviewHint: String(item?.audit?.reviewHint || '').trim(),
    openIssueRefs: Array.isArray(item?.audit?.openIssueRefs) ? item.audit.openIssueRefs : [],
    repoRefs: Array.isArray(item?.audit?.repoRefs) ? item.audit.repoRefs : [],
    repoRefSummary: item?.audit?.repoRefSummary || { automation: 0, plan: 0, code: 0, history: 0 },
  }));

const loadReferenceAudits = (referenceAuditDir, reviewedManifest) => {
  const triagePath = String(reviewedManifest?.reviewedDecisions?.sourceTriagePath || '');
  const inventory = reviewedManifest?.sourceInventory || {};
  const audits = {};

  for (const filename of AUDIT_FILENAMES) {
    const targetPath = path.join(referenceAuditDir, filename);
    if (!fs.existsSync(targetPath)) continue;
    const payload = readJson(targetPath);
    const sourceTriage = payload?.sourceTriage || {};
    if (triagePath && String(sourceTriage.path || '') !== triagePath) {
      throw new Error(`${filename} sourceTriage.path does not match reviewed manifest source triage`);
    }
    if (String(sourceTriage.base || '') !== String(inventory.base || '')) {
      throw new Error(`${filename} sourceTriage.base does not match reviewed manifest source inventory base`);
    }
    if (String(sourceTriage.remote || '') !== String(inventory.remote || '')) {
      throw new Error(`${filename} sourceTriage.remote does not match reviewed manifest source inventory remote`);
    }
    audits[payload?.batch?.id || filename] = {
      path: targetPath,
      payload,
      itemsByBranch: new Map(normalizeAuditItems(payload).map((item) => [item.branch, item])),
    };
  }

  return audits;
};

const hasBlockingRefs = (auditItem) =>
  auditItem.openIssueRefs.length > 0 ||
  Number(auditItem.repoRefSummary.automation || 0) > 0 ||
  Number(auditItem.repoRefSummary.plan || 0) > 0 ||
  Number(auditItem.repoRefSummary.code || 0) > 0;

const summarizeByBatch = (items) => {
  const batches = {
    B: { id: 'B', title: 'Low-risk stale branches', total: 0, 'delete-ready': 0, 'delete-blocked': 0, retained: 0, 'pending-review': 0, 'missing-audit': 0 },
    C: { id: 'C', title: 'Ambiguous stale branches', total: 0, 'delete-ready': 0, 'delete-blocked': 0, retained: 0, 'pending-review': 0, 'missing-audit': 0 },
  };

  for (const item of items) {
    if (!batches[item.batchId]) continue;
    batches[item.batchId].total += 1;
    batches[item.batchId][item.status] += 1;
  }
  return batches;
};

const summarizeOverall = (items) =>
  Object.fromEntries(STATUS_ORDER.map((status) => [status, items.filter((item) => item.status === status).length]));

const buildReviewedStatus = (reviewedManifest, audits) => {
  const remoteStale = Array.isArray(reviewedManifest?.remoteStale) ? reviewedManifest.remoteStale : [];
  const items = [];

  for (const item of remoteStale) {
    const batchId = classifyBatchId(item);
    if (!batchId) continue;

    const audit = audits[batchId]?.itemsByBranch?.get(String(item.branch || '').trim()) || null;
    let status = 'pending-review';

    if (!audit) {
      status = 'missing-audit';
    } else if (!item.decision) {
      status = 'pending-review';
    } else if (item.decision === 'keep' || item.decision === 'archive') {
      status = 'retained';
    } else if (item.decision === 'delete' && hasBlockingRefs(audit)) {
      status = 'delete-blocked';
    } else if (item.decision === 'delete') {
      status = 'delete-ready';
    }

    items.push({
      batchId,
      branch: item.branch,
      branchOid: item.branchOid || '',
      ageDays: item.ageDays,
      riskBand: item.riskBand || '',
      prState: item.prState || '',
      prMatchMode: item.prMatchMode || '',
      latestPr: item.latestPr || null,
      proposedAction: item.proposedAction || '',
      decision: item.decision || '',
      notes: item.notes || '',
      status,
      audit: audit
        ? {
            reviewHint: audit.reviewHint,
            openIssueRefs: audit.openIssueRefs,
            repoRefSummary: audit.repoRefSummary,
          }
        : null,
    });
  }

  return items;
};

const buildBranchListPayload = (items) => ({
  branches: items.map((item) => ({
    branch: item.branch,
    branchOid: item.branchOid || '',
    decision: item.decision || '',
    prState: item.prState || '',
  })),
});

const renderSummaryMarkdown = (summary) => {
  const rows = Object.values(summary.batches).map((item) => [
    item.id,
    item.title,
    String(item.total),
    String(item['delete-ready']),
    String(item['delete-blocked']),
    String(item.retained),
    String(item['pending-review']),
    String(item['missing-audit']),
  ]);

  return `# Remote Cleanup Review Status

- generatedAt: ${summary.generatedAt}
- reviewed manifest: \`${summary.source.reviewedManifestPath}\`
- reference audit dir: \`${summary.source.referenceAuditDir}\`
- source triage: \`${summary.source.sourceTriagePath}\`

${renderTable(['batch', 'title', 'total', 'deleteReady', 'deleteBlocked', 'retained', 'pending', 'missingAudit'], rows)}

## Overall

- delete-ready: ${summary.overall['delete-ready']}
- delete-blocked: ${summary.overall['delete-blocked']}
- retained: ${summary.overall.retained}
- pending-review: ${summary.overall['pending-review']}
- missing-audit: ${summary.overall['missing-audit']}
`;
};

const renderStatusMarkdown = (title, items) => {
  const rows = items.map((item) => [
    `\`${item.branch}\``,
    item.batchId,
    item.branchOid || '-',
    item.prState || '-',
    item.decision || '(none)',
    String(item.audit?.openIssueRefs?.length || 0),
    String(item.audit?.repoRefSummary?.automation || 0),
    String(item.audit?.repoRefSummary?.plan || 0),
    String(item.audit?.repoRefSummary?.code || 0),
    item.notes || '',
  ]);

  return `# ${title}

${renderTable(['branch', 'batch', 'branchOid', 'prState', 'decision', 'openIssues', 'automation', 'plan', 'code', 'notes'], rows)}
`;
};

const renderIssueComment = (summary) => `Review status refresh from \`${summary.source.reviewedManifestPath}\`:
- delete-ready: ${summary.overall['delete-ready']}
- delete-blocked: ${summary.overall['delete-blocked']}
- retained: ${summary.overall.retained}
- pending-review: ${summary.overall['pending-review']}
- missing-audit: ${summary.overall['missing-audit']}

Batch breakdown:
- Batch B: total=${summary.batches.B.total}, ready=${summary.batches.B['delete-ready']}, blocked=${summary.batches.B['delete-blocked']}, retained=${summary.batches.B.retained}, pending=${summary.batches.B['pending-review']}
- Batch C: total=${summary.batches.C.total}, ready=${summary.batches.C['delete-ready']}, blocked=${summary.batches.C['delete-blocked']}, retained=${summary.batches.C.retained}, pending=${summary.batches.C['pending-review']}

Artifacts:
- \`delete-ready.branches.txt\`
- \`delete-ready.branches.json\`
- \`delete-blocked.json\`
- \`pending-review.json\`
- \`retained.json\`

Notes:
- this step does not execute any remote delete
- \`delete-ready.branches.json\` is the narrow input for explicit operator-approved stale delete runs
`;

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const reviewedManifestPath = path.resolve(options.reviewedManifestJson);
  const referenceAuditDir = path.resolve(options.referenceAuditDir);
  const outputDir = path.resolve(options.outputDir);

  const reviewedManifest = readJson(reviewedManifestPath);
  const audits = loadReferenceAudits(referenceAuditDir, reviewedManifest);
  const reviewedItems = buildReviewedStatus(reviewedManifest, audits);
  const byStatus = Object.fromEntries(STATUS_ORDER.map((status) => [status, reviewedItems.filter((item) => item.status === status)]));

  const summary = {
    generatedAt: new Date().toISOString(),
    source: {
      reviewedManifestPath,
      referenceAuditDir,
      sourceTriagePath: reviewedManifest?.reviewedDecisions?.sourceTriagePath || '',
    },
    mergedAudit: audits.A
      ? {
          total: Number(audits.A.payload?.summary?.total || 0),
          clearCandidates: Number(audits.A.payload?.summary?.clearCandidates || 0),
        }
      : null,
    overall: summarizeOverall(reviewedItems),
    batches: summarizeByBatch(reviewedItems),
  };

  writeFile(path.join(outputDir, 'summary.json'), `${JSON.stringify(summary, null, 2)}\n`);
  writeFile(path.join(outputDir, 'summary.md'), renderSummaryMarkdown(summary));
  writeFile(path.join(outputDir, 'issue-comment.md'), renderIssueComment(summary));
  writeFile(path.join(outputDir, 'delete-ready.json'), `${JSON.stringify(byStatus['delete-ready'], null, 2)}\n`);
  writeFile(path.join(outputDir, 'delete-ready.md'), renderStatusMarkdown('Delete Ready', byStatus['delete-ready']));
  writeFile(path.join(outputDir, 'delete-ready.branches.txt'), `${byStatus['delete-ready'].map((item) => item.branch).join('\n')}${byStatus['delete-ready'].length ? '\n' : ''}`);
  writeFile(path.join(outputDir, 'delete-ready.branches.json'), `${JSON.stringify(buildBranchListPayload(byStatus['delete-ready']), null, 2)}\n`);
  writeFile(path.join(outputDir, 'delete-blocked.json'), `${JSON.stringify(byStatus['delete-blocked'], null, 2)}\n`);
  writeFile(path.join(outputDir, 'pending-review.json'), `${JSON.stringify(byStatus['pending-review'], null, 2)}\n`);
  writeFile(path.join(outputDir, 'retained.json'), `${JSON.stringify(byStatus.retained, null, 2)}\n`);
  writeFile(path.join(outputDir, 'missing-audit.json'), `${JSON.stringify(byStatus['missing-audit'], null, 2)}\n`);

  console.log(`[remote-cleanup-review-status] wrote ${path.join(outputDir, 'summary.json')}`);
  console.log(`[remote-cleanup-review-status] ready=${summary.overall['delete-ready']} blocked=${summary.overall['delete-blocked']} pending=${summary.overall['pending-review']}`);
};

const currentFilePath = fileURLToPath(import.meta.url);
if (process.argv[1] && path.resolve(process.argv[1]) === currentFilePath) {
  try {
    run();
  } catch (error) {
    console.error('[remote-cleanup-review-status] ERROR:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}
