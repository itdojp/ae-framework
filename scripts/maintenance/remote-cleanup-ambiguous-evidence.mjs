#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { renderCsv } from './remote-cleanup-csv.mjs';
import { renderTable } from './remote-branch-triage.mjs';

const DEFAULT_BATCH_JSON = 'tmp/maintenance/remote-cleanup-batches/batch-c-ambiguous-stale.json';
const DEFAULT_AUDIT_JSON = 'tmp/maintenance/remote-cleanup-reference-audit/batch-c-ambiguous-stale.audit.json';
const DEFAULT_OUTPUT_DIR = 'tmp/maintenance/remote-cleanup-ambiguous-evidence';

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-cleanup-ambiguous-evidence.mjs [options]

Options:
  --batch-json <path>   Batch C review pack JSON path (default: ${DEFAULT_BATCH_JSON})
  --audit-json <path>   Batch C reference audit JSON path (default: ${DEFAULT_AUDIT_JSON})
  --output-dir <path>   Output directory for ambiguous evidence artifacts (default: ${DEFAULT_OUTPUT_DIR})
  --help                Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    batchJson: DEFAULT_BATCH_JSON,
    auditJson: DEFAULT_AUDIT_JSON,
    outputDir: DEFAULT_OUTPUT_DIR,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--batch-json') {
      options.batchJson = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--audit-json') {
      options.auditJson = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = String(argv[++index] || '').trim();
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.batchJson) throw new Error('--batch-json is required');
  if (!options.auditJson) throw new Error('--audit-json is required');
  if (!options.outputDir) throw new Error('--output-dir is required');
  return options;
};

const readJson = (targetPath) => JSON.parse(fs.readFileSync(targetPath, 'utf8'));

const writeFile = (targetPath, content) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
};

const formatLatestPr = (latestPr) => {
  if (!latestPr?.number) return '-';
  const state = String(latestPr.state || latestPr.status || '').trim();
  return state ? `#${latestPr.number} (${state})` : `#${latestPr.number}`;
};

const summarizeRepoRefs = (repoRefs) =>
  repoRefs.reduce(
    (accumulator, item) => {
      const category = String(item?.category || '').trim();
      if (Object.hasOwn(accumulator, category)) accumulator[category] += 1;
      return accumulator;
    },
    { automation: 0, plan: 0, code: 0, history: 0 },
  );

const formatIssueRefs = (refs) =>
  refs
    .slice(0, 3)
    .map((item) => `#${item.number} ${item.source}`)
    .join(', ') || '-';

const formatRepoRefs = (refs) =>
  refs
    .slice(0, 3)
    .map((item) => `${item.path}${item.lineMatches?.[0] ? `:${item.lineMatches[0].line}` : ''}`)
    .join(', ') || '-';

const ensureBatchC = (payload, label) => {
  if (!payload || typeof payload !== 'object') throw new Error(`${label} is not a JSON object`);
  if (String(payload?.batch?.id || '') !== 'C') throw new Error(`${label} must be a Batch C payload`);
  if (!Array.isArray(payload?.items)) throw new Error(`${label} is missing items[]`);
  if (!payload?.sourceTriage || typeof payload.sourceTriage !== 'object') {
    throw new Error(`${label} is missing sourceTriage`);
  }
};

const validateSourceTriage = (batchPayload, auditPayload) => {
  const expected = batchPayload.sourceTriage || {};
  const actual = auditPayload.sourceTriage || {};
  for (const field of ['path', 'generatedAt', 'inventoryGeneratedAt', 'base', 'remote']) {
    if (String(expected[field] || '') !== String(actual[field] || '')) {
      throw new Error(`sourceTriage.${field} mismatch between batch JSON and audit JSON`);
    }
  }
};

const indexUniqueByBranch = (items, label) => {
  const byBranch = new Map();
  for (const item of items) {
    const branch = String(item?.branch || '').trim();
    if (!branch) throw new Error(`${label} contains a row without branch`);
    if (byBranch.has(branch)) throw new Error(`${label} contains duplicate branch rows: ${branch}`);
    byBranch.set(branch, item);
  }
  return byBranch;
};

const buildEvidenceRows = (batchPayload, auditPayload) => {
  const batchByBranch = indexUniqueByBranch(batchPayload.items, 'batch JSON');
  const auditByBranch = indexUniqueByBranch(auditPayload.items, 'audit JSON');

  if (batchByBranch.size !== auditByBranch.size) {
    throw new Error('batch JSON and audit JSON contain different branch counts');
  }

  const rows = [];
  for (const [branch, batchItem] of batchByBranch.entries()) {
    const auditItem = auditByBranch.get(branch);
    if (!auditItem) throw new Error(`audit JSON is missing branch row: ${branch}`);
    const batchOid = String(batchItem.branchOid || '').trim();
    const auditOid = String(auditItem.branchOid || '').trim();
    if (batchOid !== auditOid) {
      throw new Error(`branchOid mismatch for ${branch}`);
    }

    const issueRefs = Array.isArray(auditItem?.audit?.openIssueRefs) ? auditItem.audit.openIssueRefs : [];
    const repoRefs = Array.isArray(auditItem?.audit?.repoRefs) ? auditItem.audit.repoRefs : [];
    const repoRefSummary =
      auditItem?.audit?.repoRefSummary && typeof auditItem.audit.repoRefSummary === 'object'
        ? auditItem.audit.repoRefSummary
        : summarizeRepoRefs(repoRefs);

    rows.push({
      branch,
      ageDays: Number(batchItem.ageDays || 0),
      branchOid: batchOid,
      riskBand: String(batchItem.riskBand || '').trim(),
      prState: String(batchItem.prState || '').trim(),
      prMatchMode: String(batchItem.prMatchMode || '').trim(),
      latestPr: batchItem.latestPr || null,
      latestPrLabel: formatLatestPr(batchItem.latestPr),
      baseBranches: Array.isArray(batchItem.baseBranches) ? batchItem.baseBranches : [],
      proposedAction: String(batchItem.proposedAction || '').trim(),
      reviewHint: String(auditItem?.audit?.reviewHint || 'manual-review').trim() || 'manual-review',
      openIssueRefs: issueRefs,
      repoRefs,
      repoRefSummary: {
        automation: Number(repoRefSummary.automation || 0),
        plan: Number(repoRefSummary.plan || 0),
        code: Number(repoRefSummary.code || 0),
        history: Number(repoRefSummary.history || 0),
      },
    });
  }

  return rows.sort((left, right) => left.branch.localeCompare(right.branch));
};

const countBy = (items, selector, keys) =>
  Object.fromEntries(keys.map((key) => [key, items.filter((item) => selector(item) === key).length]));

const renderSummaryMarkdown = (summary) => {
  const rows = summary.items.map((item) => [
    `\`${item.branch}\``,
    String(item.ageDays),
    item.prMatchMode || '-',
    item.latestPrLabel,
    item.reviewHint,
    String(item.openIssueRefs.length),
    String(item.repoRefSummary.automation),
    String(item.repoRefSummary.plan),
    String(item.repoRefSummary.code),
    formatIssueRefs(item.openIssueRefs),
    formatRepoRefs(item.repoRefs),
  ]);

  return `# Remote Cleanup Ambiguous Evidence

- generatedAt: ${summary.generatedAt}
- batch JSON: \`${summary.source.batchJsonPath}\`
- audit JSON: \`${summary.source.auditJsonPath}\`
- source triage: \`${summary.source.sourceTriage.path}\`

${renderTable(
    ['branch', 'ageDays', 'match', 'latestPr', 'reviewHint', 'openIssues', 'automation', 'plan', 'code', 'issueRefs', 'repoRefs'],
    rows,
  )}

## Totals

- total branches: ${summary.counts.total}
- keep-review: ${summary.counts.reviewHints['keep-review']}
- manual-review: ${summary.counts.reviewHints['manual-review']}
- with open issue refs: ${summary.counts.withOpenIssueRefs}
- with automation refs: ${summary.counts.withAutomationRefs}
- with plan refs: ${summary.counts.withPlanRefs}
- with code refs: ${summary.counts.withCodeRefs}
- clear of active refs: ${summary.counts.clearOfActiveRefs}
`;
};

const renderIssueComment = (summary) => {
  const topBranches = summary.items
    .slice(0, 5)
    .map(
      (item) =>
        `- ${item.branch}: match=${item.prMatchMode || '-'}, latestPr=${item.latestPrLabel}, reviewHint=${item.reviewHint}, refs=open:${item.openIssueRefs.length}/automation:${item.repoRefSummary.automation}/plan:${item.repoRefSummary.plan}/code:${item.repoRefSummary.code}`,
    )
    .join('\n');

  return `Ambiguous Batch C evidence from \`${summary.source.auditJsonPath}\`:
- total: ${summary.counts.total}
- keep-review: ${summary.counts.reviewHints['keep-review']}
- manual-review: ${summary.counts.reviewHints['manual-review']}
- with open issue refs: ${summary.counts.withOpenIssueRefs}
- with automation refs: ${summary.counts.withAutomationRefs}
- with plan refs: ${summary.counts.withPlanRefs}
- with code refs: ${summary.counts.withCodeRefs}
- clear of active refs: ${summary.counts.clearOfActiveRefs}

Top rows:
${topBranches || '- (none)'}

Notes:
- this bundle is evidence only; it does not change any decision
- use it together with \`batch-c-ambiguous-stale.csv\` when entering operator decisions
`;
};

const renderEvidenceCsv = (items) =>
  renderCsv(
    [
      'branch',
      'ageDays',
      'branchOid',
      'riskBand',
      'prState',
      'prMatchMode',
      'latestPr',
      'baseBranches',
      'proposedAction',
      'reviewHint',
      'openIssueCount',
      'automationCount',
      'planCount',
      'codeCount',
      'issueRefs',
      'repoRefs',
    ],
    items.map((item) => ({
      branch: item.branch,
      ageDays: String(item.ageDays),
      branchOid: item.branchOid,
      riskBand: item.riskBand,
      prState: item.prState,
      prMatchMode: item.prMatchMode,
      latestPr: item.latestPrLabel,
      baseBranches: item.baseBranches.join(' '),
      proposedAction: item.proposedAction,
      reviewHint: item.reviewHint,
      openIssueCount: String(item.openIssueRefs.length),
      automationCount: String(item.repoRefSummary.automation),
      planCount: String(item.repoRefSummary.plan),
      codeCount: String(item.repoRefSummary.code),
      issueRefs: formatIssueRefs(item.openIssueRefs),
      repoRefs: formatRepoRefs(item.repoRefs),
    })),
  );

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const batchJsonPath = path.resolve(options.batchJson);
  const auditJsonPath = path.resolve(options.auditJson);
  const outputDir = path.resolve(options.outputDir);

  const batchPayload = readJson(batchJsonPath);
  const auditPayload = readJson(auditJsonPath);
  ensureBatchC(batchPayload, 'batch JSON');
  ensureBatchC(auditPayload, 'audit JSON');
  validateSourceTriage(batchPayload, auditPayload);

  const items = buildEvidenceRows(batchPayload, auditPayload);
  const counts = {
    total: items.length,
    reviewHints: countBy(items, (item) => item.reviewHint, ['keep-review', 'manual-review']),
    withOpenIssueRefs: items.filter((item) => item.openIssueRefs.length > 0).length,
    withAutomationRefs: items.filter((item) => item.repoRefSummary.automation > 0).length,
    withPlanRefs: items.filter((item) => item.repoRefSummary.plan > 0).length,
    withCodeRefs: items.filter((item) => item.repoRefSummary.code > 0).length,
    clearOfActiveRefs: items.filter(
      (item) =>
        item.openIssueRefs.length === 0 &&
        item.repoRefSummary.automation === 0 &&
        item.repoRefSummary.plan === 0 &&
        item.repoRefSummary.code === 0,
    ).length,
  };

  const summary = {
    generatedAt: new Date().toISOString(),
    source: {
      batchJsonPath,
      auditJsonPath,
      sourceTriage: auditPayload.sourceTriage,
    },
    counts,
    items,
  };

  writeFile(path.join(outputDir, 'summary.json'), `${JSON.stringify(summary, null, 2)}\n`);
  writeFile(path.join(outputDir, 'summary.md'), renderSummaryMarkdown(summary));
  writeFile(path.join(outputDir, 'issue-comment.md'), renderIssueComment(summary));
  writeFile(path.join(outputDir, 'ambiguous-evidence.csv'), renderEvidenceCsv(items));

  console.log(`[remote-cleanup-ambiguous-evidence] wrote ${path.join(outputDir, 'summary.json')}`);
  console.log(
    `[remote-cleanup-ambiguous-evidence] total=${summary.counts.total} keep=${summary.counts.reviewHints['keep-review']} manual=${summary.counts.reviewHints['manual-review']}`,
  );
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error('[remote-cleanup-ambiguous-evidence] ERROR:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}
