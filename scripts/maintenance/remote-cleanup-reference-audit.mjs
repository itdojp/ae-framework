#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { renderTable } from './remote-branch-triage.mjs';

const DEFAULT_BATCH_DIR = 'tmp/maintenance/remote-cleanup-batches';
const DEFAULT_OUTPUT_DIR = 'tmp/maintenance/remote-cleanup-reference-audit';
const DEFAULT_OWNER = 'itdojp';
const DEFAULT_REPO = 'ae-framework';
const DEFAULT_MATCH_LIMIT = 3;
const COMMAND_MAX_BUFFER = 16 * 1024 * 1024;

const EXCLUDED_PREFIXES = ['tmp/', 'artifacts/', 'coverage/', 'dist/', 'node_modules/'];
const HISTORY_PATTERNS = [
  /^docs\/maintenance\/branch-cleanup-report-/,
  /^docs\/maintenance\/todo-triage-/,
  /^docs\/maintenance\/phase\d+-inventory-/,
];
const BATCH_FILENAMES = [
  'batch-a-merged.json',
  'batch-b-low-risk-stale.json',
  'batch-c-ambiguous-stale.json',
];

const usage = () => {
  console.log(`Usage: node scripts/maintenance/remote-cleanup-reference-audit.mjs [options]

Options:
  --batch-dir <path>          Directory containing review pack JSON files (default: ${DEFAULT_BATCH_DIR})
  --output-dir <path>         Output directory for audit reports (default: ${DEFAULT_OUTPUT_DIR})
  --owner <name>              GitHub owner for open issue lookup (default: ${DEFAULT_OWNER})
  --repo <name>               GitHub repo for open issue lookup (default: ${DEFAULT_REPO})
  --open-issues-json <path>   Offline JSON fixture for open issues/comments
  --ignore-issue-number <n>   Ignore matching open issue numbers (repeatable)
  --match-limit <n>           Per-file / per-issue line match limit (default: ${DEFAULT_MATCH_LIMIT})
  --skip-open-issues          Skip GitHub open issue lookup
  --help                      Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    batchDir: DEFAULT_BATCH_DIR,
    outputDir: DEFAULT_OUTPUT_DIR,
    owner: DEFAULT_OWNER,
    repo: DEFAULT_REPO,
    openIssuesJson: '',
    ignoreIssueNumbers: [],
    matchLimit: DEFAULT_MATCH_LIMIT,
    skipOpenIssues: false,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--batch-dir') {
      options.batchDir = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--owner') {
      options.owner = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--repo') {
      options.repo = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--open-issues-json') {
      options.openIssuesJson = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--ignore-issue-number') {
      const value = Number(argv[++i]);
      if (!Number.isInteger(value) || value < 1) {
        throw new Error('--ignore-issue-number must be a positive integer');
      }
      options.ignoreIssueNumbers.push(value);
      continue;
    }
    if (arg === '--match-limit') {
      options.matchLimit = Number(argv[++i]);
      continue;
    }
    if (arg === '--skip-open-issues') {
      options.skipOpenIssues = true;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.batchDir) throw new Error('--batch-dir is required');
  if (!options.outputDir) throw new Error('--output-dir is required');
  if (!options.owner) throw new Error('--owner is required');
  if (!options.repo) throw new Error('--repo is required');
  if (!Number.isInteger(options.matchLimit) || options.matchLimit < 1) {
    throw new Error('--match-limit must be a positive integer');
  }
  return options;
};

const runCommand = (command, args, { cwd = process.cwd() } = {}) =>
  {
    try {
      return execFileSync(command, args, {
        cwd,
        encoding: 'utf8',
        maxBuffer: COMMAND_MAX_BUFFER,
        stdio: ['ignore', 'pipe', 'pipe'],
      }).trimEnd();
    } catch (error) {
      const stdout = error && typeof error === 'object' && 'stdout' in error ? String(error.stdout || '') : '';
      const stderr = error && typeof error === 'object' && 'stderr' in error ? String(error.stderr || '') : '';
      throw new Error(
        `${command} ${args.join(' ')} failed${stdout || stderr ? `\nstdout=${stdout}\nstderr=${stderr}` : ''}`,
      );
    }
  };

const runGh = (args) => runCommand('gh', args);

const readJson = (targetPath) => JSON.parse(fs.readFileSync(targetPath, 'utf8'));

export const flattenPaginatedRestPages = (payload) => {
  if (!Array.isArray(payload)) return [];
  return payload.flatMap((entry) => (Array.isArray(entry) ? entry : [entry]));
};

const ensurePerPage = (endpoint) => {
  const separator = endpoint.includes('?') ? '&' : '?';
  return endpoint.includes('per_page=') ? endpoint : `${endpoint}${separator}per_page=100`;
};

const loadPaginatedGhItems = (endpoint, ghRunner = runGh) =>
  flattenPaginatedRestPages(JSON.parse(ghRunner(['api', '--paginate', '--slurp', ensurePerPage(endpoint)])));

const isHistoryPath = (relativePath) => HISTORY_PATTERNS.some((pattern) => pattern.test(relativePath));

export const classifyRepoPath = (relativePath) => {
  if (EXCLUDED_PREFIXES.some((prefix) => relativePath.startsWith(prefix))) return 'excluded';
  if (isHistoryPath(relativePath)) return 'history';
  if (relativePath.startsWith('.github/')) return 'automation';
  if (relativePath.startsWith('scripts/')) return 'automation';
  if (relativePath === 'README.md' || relativePath === 'AGENTS.md') return 'plan';
  if (relativePath.startsWith('docs/')) return 'plan';
  return 'code';
};

const extractLineMatches = (content, token, limit) => {
  const matches = [];
  const lines = String(content).split(/\r?\n/);
  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    if (!line.includes(token)) continue;
    matches.push({ line: index + 1, text: line.trim() });
    if (matches.length >= limit) break;
  }
  return matches;
};

const loadTrackedFiles = (repoRoot) => {
  const output = runCommand('git', ['ls-files', '-z'], { cwd: repoRoot });
  return output
    .split('\0')
    .map((item) => item.trim())
    .filter(Boolean);
};

export const scanRepoReferences = (repoRoot, branches, { matchLimit = DEFAULT_MATCH_LIMIT } = {}) => {
  const refsByBranch = new Map(branches.map((branch) => [branch, []]));
  const files = loadTrackedFiles(repoRoot);

  for (const relativePath of files) {
    const category = classifyRepoPath(relativePath);
    if (category === 'excluded') continue;
    const absolutePath = path.join(repoRoot, relativePath);
    let content = '';
    try {
      content = fs.readFileSync(absolutePath, 'utf8');
    } catch {
      continue;
    }
    if (content.includes('\0')) continue;

    for (const branch of branches) {
      if (!content.includes(branch)) continue;
      const lineMatches = extractLineMatches(content, branch, matchLimit);
      refsByBranch.get(branch).push({
        path: relativePath,
        category,
        lineMatches,
      });
    }
  }

  return refsByBranch;
};

const normalizeOpenIssueFixture = (items) =>
  items.map((item) => ({
    number: item.number,
    title: item.title || '',
    body: item.body || '',
    url: item.html_url || item.url || '',
    isPullRequest: Boolean(item.pull_request),
    comments: Array.isArray(item.comments_data)
      ? item.comments_data
      : Array.isArray(item.comments)
        ? item.comments
        : [],
  }));

export const loadOpenIssues = ({
  owner,
  repo,
  openIssuesJson = '',
  skipOpenIssues = false,
  ghRunner = runGh,
} = {}) => {
  if (skipOpenIssues) {
    return {
      available: false,
      reason: 'skipped',
      items: [],
    };
  }

  if (openIssuesJson) {
    return {
      available: true,
      reason: 'fixture',
      items: normalizeOpenIssueFixture(readJson(openIssuesJson)),
    };
  }

  const baseItems = loadPaginatedGhItems(`repos/${owner}/${repo}/issues?state=open`, ghRunner);
  const items = baseItems.map((item) => {
    let comments = [];
    if (item.comments > 0 && item.comments_url) {
      comments = loadPaginatedGhItems(item.comments_url, ghRunner);
    }
    return {
      number: item.number,
      title: item.title || '',
      body: item.body || '',
      url: item.html_url || '',
      isPullRequest: Boolean(item.pull_request),
      comments,
    };
  });

  return {
    available: true,
    reason: 'live',
    items,
  };
};

export const scanOpenIssueReferences = (
  issuesResult,
  branches,
  { matchLimit = DEFAULT_MATCH_LIMIT, ignoreIssueNumbers = [] } = {},
) => {
  const refsByBranch = new Map(branches.map((branch) => [branch, []]));
  if (!issuesResult.available) return refsByBranch;
  const ignored = new Set(ignoreIssueNumbers);

  for (const item of issuesResult.items) {
    if (ignored.has(item.number)) continue;
    for (const branch of branches) {
      if (String(item.title).includes(branch)) {
        refsByBranch.get(branch).push({
          source: item.isPullRequest ? 'open-pr-title' : 'open-issue-title',
          number: item.number,
          title: item.title,
          url: item.url,
          matches: [{ line: 1, text: item.title }],
        });
      }
      if (String(item.body).includes(branch)) {
        refsByBranch.get(branch).push({
          source: item.isPullRequest ? 'open-pr-body' : 'open-issue-body',
          number: item.number,
          title: item.title,
          url: item.url,
          matches: extractLineMatches(item.body, branch, matchLimit),
        });
      }
      for (const comment of item.comments || []) {
        const body = String(comment.body || '');
        if (!body.includes(branch)) continue;
        refsByBranch.get(branch).push({
          source: item.isPullRequest ? 'open-pr-comment' : 'open-issue-comment',
          number: item.number,
          title: item.title,
          url: comment.html_url || item.url,
          matches: extractLineMatches(body, branch, matchLimit),
        });
      }
    }
  }

  return refsByBranch;
};

const summarizeRepoRefs = (refs) => ({
  automation: refs.filter((item) => item.category === 'automation').length,
  plan: refs.filter((item) => item.category === 'plan').length,
  code: refs.filter((item) => item.category === 'code').length,
  history: refs.filter((item) => item.category === 'history').length,
});

const deriveReviewHint = ({ batchId, item, issueRefs, repoRefs }) => {
  const repoSummary = summarizeRepoRefs(repoRefs);
  if (issueRefs.length > 0 || repoSummary.automation > 0) return 'keep-review';
  if (repoSummary.plan > 0 || repoSummary.code > 0) return 'manual-review';
  if (batchId === 'C' || item.prState === 'ambiguous') return 'manual-review';
  if (item.proposedAction === 'archive-review') return 'archive-candidate';
  if (item.proposedAction === 'delete-review' || item.proposedAction === 'delete') return 'delete-candidate';
  return 'manual-review';
};

const formatIssueRefs = (refs) =>
  refs
    .slice(0, 3)
    .map((item) => `#${item.number} ${item.source}`)
    .join(', ') || '-';

const formatRepoRefs = (refs) =>
  refs
    .slice(0, 3)
    .map((item) => `${item.path}${item.lineMatches[0] ? `:${item.lineMatches[0].line}` : ''}`)
    .join(', ') || '-';

const buildBatchAudit = (batchPayload, issueRefsByBranch, repoRefsByBranch) => {
  const items = batchPayload.items.map((item) => {
    const issueRefs = issueRefsByBranch.get(item.branch) || [];
    const repoRefs = repoRefsByBranch.get(item.branch) || [];
    const repoSummary = summarizeRepoRefs(repoRefs);
    const reviewHint = deriveReviewHint({
      batchId: batchPayload.batch.id,
      item,
      issueRefs,
      repoRefs,
    });
    return {
      ...item,
      audit: {
        openIssueRefs: issueRefs,
        repoRefs,
        repoRefSummary: repoSummary,
        reviewHint,
      },
    };
  });

  const summary = {
    total: items.length,
    withOpenIssueRefs: items.filter((item) => item.audit.openIssueRefs.length > 0).length,
    withAutomationRefs: items.filter((item) => item.audit.repoRefSummary.automation > 0).length,
    withPlanRefs: items.filter((item) => item.audit.repoRefSummary.plan > 0).length,
    withCodeRefs: items.filter((item) => item.audit.repoRefSummary.code > 0).length,
    clearCandidates: items.filter(
      (item) =>
        item.audit.openIssueRefs.length === 0 &&
        item.audit.repoRefSummary.automation === 0 &&
        item.audit.repoRefSummary.plan === 0 &&
        item.audit.repoRefSummary.code === 0,
    ).length,
  };

  return {
    generatedAt: new Date().toISOString(),
    batch: batchPayload.batch,
    sourceTriage: batchPayload.sourceTriage,
    summary,
    items,
  };
};

const renderBatchMarkdown = (audit) => {
  const rows = audit.items.map((item) => [
    `\`${item.branch}\``,
    item.audit.reviewHint,
    String(item.audit.openIssueRefs.length),
    String(item.audit.repoRefSummary.automation),
    String(item.audit.repoRefSummary.plan),
    String(item.audit.repoRefSummary.code),
    formatIssueRefs(item.audit.openIssueRefs),
    formatRepoRefs(item.audit.repoRefs),
  ]);

  return `# Batch ${audit.batch.id} Reference Audit

- generatedAt: ${audit.generatedAt}
- source triage: \`${audit.sourceTriage.path}\`
- batch title: ${audit.batch.title}
- total: ${audit.summary.total}
- with open issue refs: ${audit.summary.withOpenIssueRefs}
- with automation refs: ${audit.summary.withAutomationRefs}
- with plan refs: ${audit.summary.withPlanRefs}
- with code refs: ${audit.summary.withCodeRefs}
- clear candidates: ${audit.summary.clearCandidates}

${renderTable(
    ['branch', 'reviewHint', 'openIssues', 'automation', 'plan', 'code', 'issueRefs', 'repoRefs'],
    rows,
  )}`;
};

const renderSummaryMarkdown = (summary) => {
  const rows = Object.values(summary.batches).map((item) => [
    item.id,
    item.slug,
    item.title,
    String(item.summary.total),
    String(item.summary.withOpenIssueRefs),
    String(item.summary.withAutomationRefs),
    String(item.summary.withPlanRefs),
    String(item.summary.withCodeRefs),
    String(item.summary.clearCandidates),
  ]);

  return `# Remote Cleanup Reference Audit

- generatedAt: ${summary.generatedAt}
- batch dir: \`${summary.source.batchDir}\`
- open issue lookup: ${summary.openIssues.available ? summary.openIssues.reason : `disabled (${summary.openIssues.reason})`}
- ignored issue numbers: ${summary.openIssues.ignoredIssueNumbers.length ? summary.openIssues.ignoredIssueNumbers.join(', ') : '(none)'}

${renderTable(
    ['batch', 'slug', 'title', 'total', 'openIssues', 'automation', 'plan', 'code', 'clearCandidates'],
    rows,
  )}`;
};

const renderIssueComment = (summary) => {
  const lines = Object.values(summary.batches).map(
    (item) =>
      `- Batch ${item.id}: total=${item.summary.total}, openIssues=${item.summary.withOpenIssueRefs}, automation=${item.summary.withAutomationRefs}, plan=${item.summary.withPlanRefs}, code=${item.summary.withCodeRefs}, clear=${item.summary.clearCandidates}`,
  );
  return `Reference audit refresh from \`${summary.source.batchDir}\`:
${lines.join('\n')}

Notes:
- clear means no open issue / automation / plan / code reference was detected in the current audit scope.
- ignored issue numbers: ${summary.openIssues.ignoredIssueNumbers.length ? summary.openIssues.ignoredIssueNumbers.join(', ') : '(none)'}
- keep-review remains required when open issue refs or automation refs exist.
- manual-review remains required for ambiguous branches and any branch with plan/code references once open issue / automation refs have cleared.
`;
};

const loadBatchPayloads = (batchDir) => {
  const payloads = [];
  for (const filename of BATCH_FILENAMES) {
    const targetPath = path.join(batchDir, filename);
    if (!fs.existsSync(targetPath)) continue;
    payloads.push({
      filename,
      path: targetPath,
      payload: readJson(targetPath),
    });
  }
  if (payloads.length === 0) {
    throw new Error(`No batch JSON files found under ${batchDir}`);
  }
  return payloads;
};

const writeFile = (targetPath, content) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
};

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const batchDir = path.resolve(options.batchDir);
  const outputDir = path.resolve(options.outputDir);
  const repoRoot = process.cwd();
  const batchPayloads = loadBatchPayloads(batchDir);
  const branches = [...new Set(batchPayloads.flatMap((entry) => entry.payload.items.map((item) => item.branch)))];

  const repoRefsByBranch = scanRepoReferences(repoRoot, branches, { matchLimit: options.matchLimit });
  const openIssues = loadOpenIssues({
    owner: options.owner,
    repo: options.repo,
    openIssuesJson: options.openIssuesJson,
    skipOpenIssues: options.skipOpenIssues,
  });
  const filteredIssueRefsByBranch = scanOpenIssueReferences(openIssues, branches, {
    matchLimit: options.matchLimit,
    ignoreIssueNumbers: options.ignoreIssueNumbers,
  });

  const audits = batchPayloads.map((entry) => {
    const audit = buildBatchAudit(entry.payload, filteredIssueRefsByBranch, repoRefsByBranch);
    const slug = path.basename(entry.filename, '.json');
    return {
      slug,
      jsonPath: path.join(outputDir, `${slug}.audit.json`),
      mdPath: path.join(outputDir, `${slug}.audit.md`),
      payload: audit,
    };
  });

  for (const audit of audits) {
    writeFile(audit.jsonPath, `${JSON.stringify(audit.payload, null, 2)}\n`);
    writeFile(audit.mdPath, renderBatchMarkdown(audit.payload));
  }

  const summary = {
    generatedAt: new Date().toISOString(),
    source: {
      batchDir,
    },
    openIssues: {
      available: openIssues.available,
      reason: openIssues.reason,
      count: openIssues.items.length,
      ignoredIssueNumbers: options.ignoreIssueNumbers,
    },
    batches: Object.fromEntries(
      audits.map((audit) => [
        audit.slug,
        {
          id: audit.payload.batch.id,
          slug: audit.slug,
          title: audit.payload.batch.title,
          summary: audit.payload.summary,
          jsonPath: audit.jsonPath,
          mdPath: audit.mdPath,
        },
      ]),
    ),
  };

  const summaryJsonPath = path.join(outputDir, 'summary.json');
  const summaryMdPath = path.join(outputDir, 'summary.md');
  const issueCommentPath = path.join(outputDir, 'issue-comment.md');
  writeFile(summaryJsonPath, `${JSON.stringify(summary, null, 2)}\n`);
  writeFile(summaryMdPath, renderSummaryMarkdown(summary));
  writeFile(issueCommentPath, renderIssueComment(summary));

  console.log(`[remote-cleanup-reference-audit] wrote ${summaryJsonPath}`);
  console.log(`[remote-cleanup-reference-audit] wrote ${summaryMdPath}`);
  console.log(`[remote-cleanup-reference-audit] batches=${audits.length} branches=${branches.length}`);
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error(`[remote-cleanup-reference-audit] ${error instanceof Error ? error.message : String(error)}`);
    process.exit(1);
  }
}
