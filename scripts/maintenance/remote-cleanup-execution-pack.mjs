#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { renderTable, shellQuote } from './remote-branch-triage.mjs';

const DEFAULT_REVIEW_STATUS_DIR = 'tmp/maintenance/remote-cleanup-review-status';
const DEFAULT_OUTPUT_DIR = 'tmp/maintenance/remote-cleanup-execution-pack';
const DEFAULT_BASE = 'origin/main';
const DEFAULT_REMOTE = 'origin';
const DEFAULT_MAX = 100;

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-cleanup-execution-pack.mjs [options]

Options:
  --review-status-dir <path>  Directory containing review-status artifacts (default: ${DEFAULT_REVIEW_STATUS_DIR})
  --output-dir <path>         Output directory for the execution pack (default: ${DEFAULT_OUTPUT_DIR})
  --base <ref>                Expected base ref recorded in the reviewed manifest (default: ${DEFAULT_BASE})
  --remote <name>             Expected remote name recorded in the reviewed manifest (default: ${DEFAULT_REMOTE})
  --max <n>                   Max branches passed to branch-cleanup dry-run/apply commands (default: ${DEFAULT_MAX})
  --help                      Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    reviewStatusDir: DEFAULT_REVIEW_STATUS_DIR,
    outputDir: DEFAULT_OUTPUT_DIR,
    base: DEFAULT_BASE,
    remote: DEFAULT_REMOTE,
    max: DEFAULT_MAX,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--review-status-dir') {
      options.reviewStatusDir = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--base') {
      options.base = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--remote') {
      options.remote = String(argv[++index] || '').trim();
      continue;
    }
    if (arg === '--max') {
      options.max = Number(argv[++index]);
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.reviewStatusDir) throw new Error('--review-status-dir is required');
  if (!options.outputDir) throw new Error('--output-dir is required');
  if (!options.base) throw new Error('--base is required');
  if (!options.remote) throw new Error('--remote is required');
  if (!Number.isInteger(options.max) || options.max < 1) {
    throw new Error('--max must be a positive integer');
  }
  return options;
};

const readJson = (targetPath) => JSON.parse(fs.readFileSync(targetPath, 'utf8'));

const writeFile = (targetPath, content, mode) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, { encoding: 'utf8', mode });
};

const readReviewStatusArtifacts = (reviewStatusDir) => {
  const summaryPath = path.join(reviewStatusDir, 'summary.json');
  const deleteReadyPath = path.join(reviewStatusDir, 'delete-ready.json');
  const deleteReadyBranchesPath = path.join(reviewStatusDir, 'delete-ready.branches.json');

  for (const targetPath of [summaryPath, deleteReadyPath, deleteReadyBranchesPath]) {
    if (!fs.existsSync(targetPath)) {
      throw new Error(`missing review-status artifact: ${targetPath}`);
    }
  }

  return {
    summaryPath,
    deleteReadyPath,
    deleteReadyBranchesPath,
    summary: readJson(summaryPath),
    deleteReady: readJson(deleteReadyPath),
    deleteReadyBranches: readJson(deleteReadyBranchesPath),
  };
};

const validateReviewedManifest = ({ reviewedManifestPath, sourceTriagePath, base, remote }) => {
  if (!reviewedManifestPath || !fs.existsSync(reviewedManifestPath)) {
    throw new Error('review-status summary is missing a valid source.reviewedManifestPath');
  }
  const reviewedManifest = readJson(reviewedManifestPath);
  const sourceInventory = reviewedManifest?.sourceInventory || {};
  if (String(sourceInventory.base || '') !== base) {
    throw new Error(`reviewed manifest base mismatch: expected ${base}, got ${String(sourceInventory.base || '')}`);
  }
  if (String(sourceInventory.remote || '') !== remote) {
    throw new Error(`reviewed manifest remote mismatch: expected ${remote}, got ${String(sourceInventory.remote || '')}`);
  }
  if (sourceTriagePath && String(reviewedManifest?.reviewedDecisions?.sourceTriagePath || '') !== sourceTriagePath) {
    throw new Error('reviewed manifest source triage path does not match review-status summary');
  }
  return reviewedManifest;
};

const normalizeDeleteReadyRows = (deleteReady, deleteReadyBranches) => {
  const rows = Array.isArray(deleteReady) ? deleteReady : [];
  const branches = Array.isArray(deleteReadyBranches?.branches) ? deleteReadyBranches.branches : [];
  if (branches.length === 0) {
    throw new Error('delete-ready branch list is empty; execution pack was not generated');
  }

  const rowByBranch = new Map();
  for (const item of rows) {
    const branch = String(item?.branch || '').trim();
    if (!branch) continue;
    rowByBranch.set(branch, item);
  }

  const seen = new Set();
  return branches.map((entry) => {
    const branch = String(entry?.branch || '').trim();
    const branchOid = String(entry?.branchOid || '').trim();
    if (!branch) {
      throw new Error('delete-ready branch entry requires branch');
    }
    if (seen.has(branch)) {
      throw new Error(`delete-ready branch list contains duplicate branch: ${branch}`);
    }
    seen.add(branch);
    const matched = rowByBranch.get(branch);
    if (!matched) {
      throw new Error(`delete-ready branch list references a branch not present in delete-ready.json: ${branch}`);
    }
    const matchedOid = String(matched?.branchOid || '').trim();
    if (branchOid && matchedOid && branchOid !== matchedOid) {
      throw new Error(`delete-ready branch OID mismatch for ${branch}`);
    }
    return {
      branch,
      branchOid: branchOid || matchedOid,
      decision: String(entry?.decision || matched?.decision || '').trim(),
      prState: String(entry?.prState || matched?.prState || '').trim(),
    };
  });
};

const runBranchCleanupDryRun = ({ reviewStatusDir, outputDir, base, remote, max }) => {
  const approvedBranchListPath = path.join(outputDir, 'approved-remote-branches.json');
  const dryRunReportPath = path.join(outputDir, 'branch-cleanup-dry-run-report.json');
  const scriptPath = fileURLToPath(new URL('./branch-cleanup.mjs', import.meta.url));
  const args = [
    scriptPath,
    '--scope',
    'remote',
    '--base',
    base,
    '--remote',
    remote,
    '--remote-branches-file',
    approvedBranchListPath,
    '--max',
    String(max),
    '--output-json',
    dryRunReportPath,
  ];
  const stdout = execFileSync(process.execPath, args, {
    cwd: process.cwd(),
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  const report = readJson(dryRunReportPath);
  return {
    command: [process.execPath, ...args],
    stdout: stdout.trim(),
    reportPath: dryRunReportPath,
    report,
    reviewStatusDir,
  };
};

const renderCommands = ({ base, remote, max, approvedBranchListPath, outputDir }) => {
  const dryRunReportPath = path.join(outputDir, 'branch-cleanup-dry-run-report.json');
  const applyReportPath = path.join(outputDir, 'branch-cleanup-apply-report.json');
  const cmdPrefix = `${shellQuote(process.execPath)} ${shellQuote('scripts/maintenance/branch-cleanup.mjs')} --scope remote --base ${shellQuote(base)} --remote ${shellQuote(remote)} --remote-branches-file ${shellQuote(approvedBranchListPath)} --max ${shellQuote(String(max))}`;
  return `#!/usr/bin/env bash
set -euo pipefail

# Generated by remote-cleanup-execution-pack.mjs
# Review the dry-run report before using the apply command.

${cmdPrefix} --output-json ${shellQuote(dryRunReportPath)}

# Execute only after operator approval has been recorded.
${cmdPrefix} --output-json ${shellQuote(applyReportPath)} --apply
`;
};

const renderSummaryMarkdown = (summary) => {
  const rows = [
    ['delete-ready rows', String(summary.deleteReady.count)],
    ['dry-run planned', String(summary.dryRun.planned)],
    ['dry-run blocked', String(summary.dryRun.blocked)],
    ['base', summary.sourceInventory.base],
    ['remote', summary.sourceInventory.remote],
  ];

  return `# Remote Cleanup Execution Pack

- generatedAt: ${summary.generatedAt}
- review status dir: \`${summary.source.reviewStatusDir}\`
- reviewed manifest: \`${summary.source.reviewedManifestPath}\`
- source triage: \`${summary.source.sourceTriagePath}\`
- dry-run report: \`${summary.artifacts.dryRunReportPath}\`
- commands: \`${summary.artifacts.commandsPath}\`

${renderTable(['item', 'value'], rows)}
`;
};

const renderIssueComment = (summary) => `Execution pack rendered from \`${summary.source.reviewStatusDir}\`:
- delete-ready rows: ${summary.deleteReady.count}
- dry-run planned: ${summary.dryRun.planned}
- dry-run blocked: ${summary.dryRun.blocked}

Artifacts:
- \`${path.basename(summary.artifacts.approvedBranchListPath)}\`
- \`${path.basename(summary.artifacts.dryRunReportPath)}\`
- \`${path.basename(summary.artifacts.commandsPath)}\`

Notes:
- this step does not delete remote branches
- run the dry-run command from \`${path.basename(summary.artifacts.commandsPath)}\` before operator-approved apply
`;

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const reviewStatusDir = path.resolve(options.reviewStatusDir);
  const outputDir = path.resolve(options.outputDir);
  const artifacts = readReviewStatusArtifacts(reviewStatusDir);
  const summarySource = artifacts.summary?.source || {};
  const reviewedManifestPath = String(summarySource.reviewedManifestPath || '').trim();
  const sourceTriagePath = String(summarySource.sourceTriagePath || '').trim();
  const reviewedManifest = validateReviewedManifest({
    reviewedManifestPath,
    sourceTriagePath,
    base: options.base,
    remote: options.remote,
  });
  const approvedBranches = normalizeDeleteReadyRows(artifacts.deleteReady, artifacts.deleteReadyBranches);

  const approvedBranchListPath = path.join(outputDir, 'approved-remote-branches.json');
  const commandsPath = path.join(outputDir, 'commands.sh');
  const approvedBranchPayload = {
    generatedAt: new Date().toISOString(),
    sourceReviewStatus: {
      dir: reviewStatusDir,
      summaryPath: artifacts.summaryPath,
      deleteReadyPath: artifacts.deleteReadyPath,
      deleteReadyBranchesPath: artifacts.deleteReadyBranchesPath,
      generatedAt: String(artifacts.summary?.generatedAt || ''),
      reviewedManifestPath,
      referenceAuditDir: String(summarySource.referenceAuditDir || ''),
      sourceTriagePath,
    },
    sourceInventory: {
      path: String(reviewedManifest?.sourceInventory?.path || ''),
      generatedAt: String(reviewedManifest?.sourceInventory?.generatedAt || ''),
      base: String(reviewedManifest?.sourceInventory?.base || ''),
      remote: String(reviewedManifest?.sourceInventory?.remote || ''),
    },
    branches: approvedBranches,
  };

  writeFile(approvedBranchListPath, `${JSON.stringify(approvedBranchPayload, null, 2)}\n`);
  writeFile(
    commandsPath,
    renderCommands({
      base: options.base,
      remote: options.remote,
      max: options.max,
      approvedBranchListPath,
      outputDir,
    }),
    0o755,
  );

  const dryRun = runBranchCleanupDryRun({
    reviewStatusDir,
    outputDir,
    base: options.base,
    remote: options.remote,
    max: options.max,
  });
  const summary = {
    generatedAt: new Date().toISOString(),
    source: {
      reviewStatusDir,
      reviewedManifestPath,
      sourceTriagePath,
      referenceAuditDir: String(summarySource.referenceAuditDir || ''),
    },
    sourceInventory: approvedBranchPayload.sourceInventory,
    deleteReady: {
      count: approvedBranches.length,
      sourceSummaryGeneratedAt: approvedBranchPayload.sourceReviewStatus.generatedAt,
    },
    dryRun: {
      planned: Array.isArray(dryRun.report?.remote?.plannedDetailed) ? dryRun.report.remote.plannedDetailed.length : 0,
      blocked: Array.isArray(dryRun.report?.remote?.blocked) ? dryRun.report.remote.blocked.length : 0,
      stdout: dryRun.stdout,
    },
    artifacts: {
      approvedBranchListPath,
      dryRunReportPath: dryRun.reportPath,
      commandsPath,
    },
  };

  writeFile(path.join(outputDir, 'summary.json'), `${JSON.stringify(summary, null, 2)}\n`);
  writeFile(path.join(outputDir, 'summary.md'), renderSummaryMarkdown(summary));
  writeFile(path.join(outputDir, 'issue-comment.md'), renderIssueComment(summary));

  console.log(`[remote-cleanup-execution-pack] wrote ${path.join(outputDir, 'summary.json')}`);
  console.log(
    `[remote-cleanup-execution-pack] delete-ready=${summary.deleteReady.count} planned=${summary.dryRun.planned} blocked=${summary.dryRun.blocked}`,
  );
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error('[remote-cleanup-execution-pack] ERROR:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}
