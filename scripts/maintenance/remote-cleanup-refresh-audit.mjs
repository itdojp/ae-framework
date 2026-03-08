#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { renderTable } from './remote-branch-triage.mjs';

const DEFAULT_POST_VERIFY_SUMMARY_JSON = 'tmp/maintenance/remote-cleanup-post-apply-verify/summary.json';
const DEFAULT_REFRESHED_TRIAGE_JSON = 'tmp/maintenance/remote-branch-triage.json';
const DEFAULT_OUTPUT_DIR = 'tmp/maintenance/remote-cleanup-refresh-audit';

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-cleanup-refresh-audit.mjs [options]

Options:
  --post-verify-summary-json <path>  Post-apply verification summary JSON (default: ${DEFAULT_POST_VERIFY_SUMMARY_JSON})
  --refreshed-triage-json <path>     Refreshed remote-branch-triage JSON (default: ${DEFAULT_REFRESHED_TRIAGE_JSON})
  --output-dir <path>                Output directory for refresh-audit artifacts (default: ${DEFAULT_OUTPUT_DIR})
  --help                             Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    postVerifySummaryJson: DEFAULT_POST_VERIFY_SUMMARY_JSON,
    refreshedTriageJson: DEFAULT_REFRESHED_TRIAGE_JSON,
    outputDir: DEFAULT_OUTPUT_DIR,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--post-verify-summary-json') {
      options.postVerifySummaryJson = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--refreshed-triage-json') {
      options.refreshedTriageJson = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = String(argv[++index] || '').trim();
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.postVerifySummaryJson) throw new Error('--post-verify-summary-json is required');
  if (!options.refreshedTriageJson) throw new Error('--refreshed-triage-json is required');
  if (!options.outputDir) throw new Error('--output-dir is required');
  return options;
};

const readJson = (targetPath) => JSON.parse(fs.readFileSync(targetPath, 'utf8'));

const writeFile = (targetPath, content) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
};

const normalizeBranchName = (item) => {
  if (typeof item === 'string') return item.trim();
  return String(item?.branch || '').trim();
};

const loadDeletedBranchesByStatus = (summary, summaryPath, acceptedStatuses) => {
  if (!Array.isArray(summary?.deleted)) {
    throw new Error(`post-verify summary is missing deleted rows: ${summaryPath}`);
  }
  return summary.deleted
    .filter((item) => acceptedStatuses.has(String(item?.status || '').trim()))
    .map((item) => ({
      branch: String(item?.branch || '').trim(),
      expectedOid: String(item?.expectedOid || '').trim(),
      actualOid: String(item?.actualOid || '').trim(),
    }))
    .filter((item) => item.branch);
};

const ensureRefreshedTriagePayload = (triage, triagePath) => {
  if (!Array.isArray(triage?.remoteMerged)) {
    throw new Error(`refreshed triage is missing remoteMerged[]: ${triagePath}`);
  }
  if (!Array.isArray(triage?.remoteStale)) {
    throw new Error(`refreshed triage is missing remoteStale[]: ${triagePath}`);
  }
};

const buildRefreshedBranchSets = (triage) => {
  const merged = new Set(
    triage.remoteMerged
      .map((item) => normalizeBranchName(item))
      .filter(Boolean),
  );
  const stale = new Set(
    triage.remoteStale
      .map((item) => normalizeBranchName(item))
      .filter(Boolean),
  );
  return { merged, stale };
};

const buildRefreshAudit = (verifiedAbsent, refreshedBranches) =>
  verifiedAbsent.map((item) => {
    const inMerged = refreshedBranches.merged.has(item.branch);
    const inStale = refreshedBranches.stale.has(item.branch);
    return {
      branch: item.branch,
      status: inMerged || inStale ? 'reappeared-in-triage' : 'confirmed-removed',
      refreshedLocations: [inMerged ? 'remoteMerged' : '', inStale ? 'remoteStale' : ''].filter(Boolean),
    };
  });

const buildRecreatedAudit = (recreatedRefs, refreshedBranches) =>
  recreatedRefs.map((item) => {
    const inMerged = refreshedBranches.merged.has(item.branch);
    const inStale = refreshedBranches.stale.has(item.branch);
    return {
      branch: item.branch,
      status: inMerged || inStale ? 'recreated-ref-in-triage' : 'recreated-ref-outside-triage',
      expectedOid: item.expectedOid || '',
      actualOid: item.actualOid || '',
      refreshedLocations: [inMerged ? 'remoteMerged' : '', inStale ? 'remoteStale' : ''].filter(Boolean),
    };
  });

const renderSummaryMarkdown = (summary) => {
  const rows = summary.audit.map((item) => [
    `\`${item.branch}\``,
    item.status,
    item.refreshedLocations.join(', ') || '-',
  ]);
  const recreatedRows = summary.recreated.map((item) => [
    `\`${item.branch}\``,
    item.status,
    item.expectedOid || '-',
    item.actualOid || '-',
    item.refreshedLocations.join(', ') || '-',
  ]);

  const recreatedSection = summary.recreated.length
    ? `## Recreated refs

${renderTable(['branch', 'status', 'expectedOid', 'actualOid', 'refreshedLocations'], recreatedRows)}

`
    : '';

  return `# Remote Cleanup Refresh Audit

- generatedAt: ${summary.generatedAt}
- post-verify summary: \`${summary.source.postVerifySummaryPath}\`
- refreshed triage: \`${summary.source.refreshedTriagePath}\`

${renderTable(['branch', 'status', 'refreshedLocations'], rows)}

${recreatedSection}## Totals

- verified-absent input: ${summary.counts.verifiedAbsentInput}
- confirmed removed: ${summary.counts.confirmedRemoved}
- reappeared in triage: ${summary.counts.reappearedInTriage}
- recreated-ref input: ${summary.counts.recreatedRefInput}
- recreated-ref in triage: ${summary.counts.recreatedRefInTriage}
- recreated-ref outside triage: ${summary.counts.recreatedRefOutsideTriage}
- refreshed remote merged candidates: ${summary.counts.refreshedRemoteMerged}
- refreshed remote stale candidates: ${summary.counts.refreshedRemoteStale}
`;
};

const renderIssueComment = (summary) => `Refresh audit from \`${summary.source.refreshedTriagePath}\`:
- verified-absent input: ${summary.counts.verifiedAbsentInput}
- confirmed removed: ${summary.counts.confirmedRemoved}
- reappeared in triage: ${summary.counts.reappearedInTriage}
- recreated-ref input: ${summary.counts.recreatedRefInput}
- recreated-ref in triage: ${summary.counts.recreatedRefInTriage}
- recreated-ref outside triage: ${summary.counts.recreatedRefOutsideTriage}
- refreshed remote merged candidates: ${summary.counts.refreshedRemoteMerged}
- refreshed remote stale candidates: ${summary.counts.refreshedRemoteStale}

Notes:
- this step performs no deletion
- branches marked \`reappeared-in-triage\` require manual follow-up before closing the cleanup batch
- branches marked \`recreated-ref-*\` indicate post-delete branch reuse and also require manual follow-up
`;

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const postVerifySummaryPath = path.resolve(options.postVerifySummaryJson);
  const refreshedTriagePath = path.resolve(options.refreshedTriageJson);
  const outputDir = path.resolve(options.outputDir);
  const postVerifySummary = readJson(postVerifySummaryPath);
  const refreshedTriage = readJson(refreshedTriagePath);

  const verifiedAbsent = loadDeletedBranchesByStatus(postVerifySummary, postVerifySummaryPath, new Set(['verified-absent']));
  const recreatedRefs = loadDeletedBranchesByStatus(postVerifySummary, postVerifySummaryPath, new Set(['recreated-ref']));
  ensureRefreshedTriagePayload(refreshedTriage, refreshedTriagePath);
  const refreshedBranches = buildRefreshedBranchSets(refreshedTriage);
  const audit = buildRefreshAudit(verifiedAbsent, refreshedBranches);
  const recreated = buildRecreatedAudit(recreatedRefs, refreshedBranches);

  const summary = {
    generatedAt: new Date().toISOString(),
    source: {
      postVerifySummaryPath,
      refreshedTriagePath,
    },
    audit,
    recreated,
    counts: {
      verifiedAbsentInput: verifiedAbsent.length,
      confirmedRemoved: audit.filter((item) => item.status === 'confirmed-removed').length,
      reappearedInTriage: audit.filter((item) => item.status === 'reappeared-in-triage').length,
      recreatedRefInput: recreated.length,
      recreatedRefInTriage: recreated.filter((item) => item.status === 'recreated-ref-in-triage').length,
      recreatedRefOutsideTriage: recreated.filter((item) => item.status === 'recreated-ref-outside-triage').length,
      refreshedRemoteMerged: Array.isArray(refreshedTriage?.remoteMerged) ? refreshedTriage.remoteMerged.length : 0,
      refreshedRemoteStale: Array.isArray(refreshedTriage?.remoteStale) ? refreshedTriage.remoteStale.length : 0,
    },
  };

  writeFile(path.join(outputDir, 'summary.json'), `${JSON.stringify(summary, null, 2)}\n`);
  writeFile(path.join(outputDir, 'summary.md'), renderSummaryMarkdown(summary));
  writeFile(path.join(outputDir, 'issue-comment.md'), renderIssueComment(summary));

  console.log(`[remote-cleanup-refresh-audit] wrote ${path.join(outputDir, 'summary.json')}`);
  console.log(
    `[remote-cleanup-refresh-audit] verifiedAbsent=${summary.counts.verifiedAbsentInput} confirmed=${summary.counts.confirmedRemoved} reappeared=${summary.counts.reappearedInTriage} recreated=${summary.counts.recreatedRefInput}`,
  );
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error('[remote-cleanup-refresh-audit] ERROR:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}
