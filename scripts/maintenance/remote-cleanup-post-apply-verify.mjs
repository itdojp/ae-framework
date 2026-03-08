#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { renderTable } from './remote-branch-triage.mjs';

const DEFAULT_CLEANUP_REPORT_JSON = 'tmp/maintenance/branch-cleanup-report.json';
const DEFAULT_OUTPUT_DIR = 'tmp/maintenance/remote-cleanup-post-apply-verify';

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-cleanup-post-apply-verify.mjs [options]

Options:
  --cleanup-report-json <path>  branch-cleanup apply report JSON (default: ${DEFAULT_CLEANUP_REPORT_JSON})
  --output-dir <path>           Output directory for verification artifacts (default: ${DEFAULT_OUTPUT_DIR})
  --help                        Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    cleanupReportJson: DEFAULT_CLEANUP_REPORT_JSON,
    outputDir: DEFAULT_OUTPUT_DIR,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--cleanup-report-json') {
      options.cleanupReportJson = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = String(argv[++index] || '').trim();
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.cleanupReportJson) throw new Error('--cleanup-report-json is required');
  if (!options.outputDir) throw new Error('--output-dir is required');
  return options;
};

const readJson = (targetPath) => JSON.parse(fs.readFileSync(targetPath, 'utf8'));

const writeFile = (targetPath, content) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
};

const runGit = (args) =>
  execFileSync('git', args, {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  }).trimEnd();

const parseLiveRemoteHeadOids = (raw) => {
  const refs = new Map();
  for (const line of raw.split('\n').map((item) => item.trim()).filter(Boolean)) {
    const [ref, oid] = line.split(/\s+/, 2);
    if (!ref || !oid || !oid.startsWith('refs/heads/')) continue;
    refs.set(oid.slice('refs/heads/'.length), ref);
  }
  return refs;
};

const validateCleanupReport = (report, reportPath) => {
  if (report?.apply !== true) {
    throw new Error(`cleanup report must be an apply run: ${reportPath}`);
  }
  if (!['remote', 'both'].includes(String(report?.scope || ''))) {
    throw new Error(`cleanup report must include remote scope: ${reportPath}`);
  }
  if (!report?.remote || typeof report.remote !== 'object') {
    throw new Error(`cleanup report is missing remote results: ${reportPath}`);
  }
  const remoteName = String(report?.remoteName || report?.remote?.selection?.expectedRemote || '').trim();
  if (!remoteName) {
    throw new Error(`cleanup report is missing remoteName: ${reportPath}`);
  }
  return remoteName;
};

const verifyDeletedBranches = (report, remoteRefs) => {
  const deleted = Array.isArray(report?.remote?.deleted) ? report.remote.deleted : [];
  const plannedDetailed = Array.isArray(report?.remote?.plannedDetailed) ? report.remote.plannedDetailed : [];
  const failed = Array.isArray(report?.remote?.failed) ? report.remote.failed : [];
  const deletedSet = new Set(deleted);
  const failedSet = new Set(failed.map((item) => item.branch));

  const deletedStatus = deleted.map((branch) => ({
    branch,
    status: remoteRefs.has(branch) ? 'still-present' : 'verified-absent',
    actualOid: remoteRefs.get(branch) || '',
  }));

  const notDeleted = plannedDetailed
    .map((item) => item.branch)
    .filter((branch) => !deletedSet.has(branch) && !failedSet.has(branch));

  return {
    deletedStatus,
    notDeleted,
  };
};

const renderSummaryMarkdown = (summary) => {
  const deletedRows = summary.deleted.map((item) => [
    `\`${item.branch}\``,
    item.status,
    item.actualOid || '-',
  ]);

  return `# Remote Cleanup Post-Apply Verification

- generatedAt: ${summary.generatedAt}
- cleanup report: \`${summary.source.cleanupReportPath}\`
- remote: \`${summary.remoteName}\`
- scope: \`${summary.scope}\`

${renderTable(['branch', 'status', 'actualOid'], deletedRows)}

## Totals

- reported deleted: ${summary.counts.reportedDeleted}
- verified absent: ${summary.counts.verifiedAbsent}
- still present: ${summary.counts.stillPresent}
- failed deletes: ${summary.counts.failedDeletes}
- blocked: ${summary.counts.blocked}
- planned but not deleted: ${summary.counts.plannedButNotDeleted}
`;
};

const renderIssueComment = (summary) => `Post-apply verification from \`${summary.source.cleanupReportPath}\`:
- reported deleted: ${summary.counts.reportedDeleted}
- verified absent: ${summary.counts.verifiedAbsent}
- still present: ${summary.counts.stillPresent}
- failed deletes: ${summary.counts.failedDeletes}
- blocked: ${summary.counts.blocked}
- planned but not deleted: ${summary.counts.plannedButNotDeleted}

Notes:
- this step performs no deletion
- rerun branch inventory and remote triage after reviewing any still-present refs
`;

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const cleanupReportPath = path.resolve(options.cleanupReportJson);
  const outputDir = path.resolve(options.outputDir);
  const report = readJson(cleanupReportPath);
  const remoteName = validateCleanupReport(report, cleanupReportPath);
  const remoteRefs = parseLiveRemoteHeadOids(runGit(['ls-remote', '--heads', remoteName]));
  const verification = verifyDeletedBranches(report, remoteRefs);
  const failedDeletes = Array.isArray(report?.remote?.failed) ? report.remote.failed : [];
  const blocked = Array.isArray(report?.remote?.blocked) ? report.remote.blocked : [];

  const summary = {
    generatedAt: new Date().toISOString(),
    source: {
      cleanupReportPath,
    },
    remoteName,
    scope: String(report.scope || ''),
    selection: report?.remote?.selection || {},
    deleted: verification.deletedStatus,
    failedDeletes,
    blocked,
    plannedButNotDeleted: verification.notDeleted,
    counts: {
      reportedDeleted: verification.deletedStatus.length,
      verifiedAbsent: verification.deletedStatus.filter((item) => item.status === 'verified-absent').length,
      stillPresent: verification.deletedStatus.filter((item) => item.status === 'still-present').length,
      failedDeletes: failedDeletes.length,
      blocked: blocked.length,
      plannedButNotDeleted: verification.notDeleted.length,
    },
  };

  writeFile(path.join(outputDir, 'summary.json'), `${JSON.stringify(summary, null, 2)}\n`);
  writeFile(path.join(outputDir, 'summary.md'), renderSummaryMarkdown(summary));
  writeFile(path.join(outputDir, 'issue-comment.md'), renderIssueComment(summary));

  console.log(`[remote-cleanup-post-apply-verify] wrote ${path.join(outputDir, 'summary.json')}`);
  console.log(
    `[remote-cleanup-post-apply-verify] deleted=${summary.counts.reportedDeleted} verified=${summary.counts.verifiedAbsent} stillPresent=${summary.counts.stillPresent}`,
  );
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error('[remote-cleanup-post-apply-verify] ERROR:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}
