#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseWorktreePorcelain } from './worktree-cleanup.mjs';

const DEFAULT_BASE_REF = 'origin/main';
const DEFAULT_REMOTE = 'origin';
const DEFAULT_OUTPUT_JSON = 'tmp/maintenance/branch-inventory.json';
const DEFAULT_OUTPUT_MD = 'tmp/maintenance/branch-inventory.md';
const DEFAULT_STALE_DAYS = 90;
const DEFAULT_TOP = 30;
const DEFAULT_GH_PR_LIMIT = 1000;
const DEFAULT_GH_PR_BASE = '';

const PROTECTED_EXACT = new Set(['main', 'master', 'develop', 'staging']);
const PROTECTED_PREFIXES = ['release/', 'hotfix/'];

const usage = () => {
  console.log(`Usage: node scripts/maintenance/branch-inventory.mjs [options]

Options:
  --base <ref>         Base ref to compare merge status (default: ${DEFAULT_BASE_REF})
  --remote <name>      Remote name (default: ${DEFAULT_REMOTE})
  --output-json <path> JSON output path (default: ${DEFAULT_OUTPUT_JSON})
  --output-md <path>   Markdown output path (default: ${DEFAULT_OUTPUT_MD})
  --stale-days <days>  Age threshold for stale branch candidates (default: ${DEFAULT_STALE_DAYS})
  --top <n>            Number of items to print in markdown sections (default: ${DEFAULT_TOP})
  --gh-pr-limit <n>    Max merged PRs to inspect via gh (default: ${DEFAULT_GH_PR_LIMIT})
  --gh-pr-base <name>  Explicit GitHub PR base branch filter (default: derived from --base)
  --help               Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    base: DEFAULT_BASE_REF,
    remote: DEFAULT_REMOTE,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    staleDays: DEFAULT_STALE_DAYS,
    top: DEFAULT_TOP,
    ghPrLimit: DEFAULT_GH_PR_LIMIT,
    ghPrBase: DEFAULT_GH_PR_BASE,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--base') {
      options.base = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--remote') {
      options.remote = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = String(argv[++i] || '').trim();
      continue;
    }
    if (arg === '--stale-days') {
      options.staleDays = Number(argv[++i]);
      continue;
    }
    if (arg === '--top') {
      options.top = Number(argv[++i]);
      continue;
    }
    if (arg === '--gh-pr-limit') {
      options.ghPrLimit = Number(argv[++i]);
      continue;
    }
    if (arg === '--gh-pr-base') {
      options.ghPrBase = String(argv[++i] || '').trim();
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.base) throw new Error('--base is required');
  if (!options.remote) throw new Error('--remote is required');
  if (!Number.isInteger(options.staleDays) || options.staleDays < 1) {
    throw new Error('--stale-days must be a positive integer');
  }
  if (!Number.isInteger(options.top) || options.top < 1) {
    throw new Error('--top must be a positive integer');
  }
  if (!Number.isInteger(options.ghPrLimit) || options.ghPrLimit < 1) {
    throw new Error('--gh-pr-limit must be a positive integer');
  }
  return options;
};

const runCommand = (command, args) =>
  execFileSync(command, args, {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  }).trimEnd();

const runCommandSafe = (command, args) => {
  try {
    return {
      ok: true,
      output: runCommand(command, args),
    };
  } catch (error) {
    const stderr = error && error.stderr ? String(error.stderr) : '';
    const stdout = error && error.stdout ? String(error.stdout) : '';
    return {
      ok: false,
      output: `${stdout}\n${stderr}`.trim(),
      message: error instanceof Error ? error.message : String(error),
    };
  }
};

const runGit = (args) => runCommand('git', args);
const runGitSafe = (args) => runCommandSafe('git', args);
const runGhSafe = (args) => runCommandSafe('gh', args);

export const parseRefs = (raw, remoteName) =>
  String(raw || '')
    .split('\n')
    .map((line) => line.trim())
    .filter(Boolean)
    .map((line) => {
      const [name, dateIso, dateUnixRaw, upstream, oid] = line.split('\t');
      const dateUnix = Number(dateUnixRaw || 0);
      const shortName = name.startsWith(`${remoteName}/`) ? name.slice(remoteName.length + 1) : name;
      return {
        name,
        shortName,
        dateIso,
        dateUnix: Number.isFinite(dateUnix) ? dateUnix : 0,
        upstream: upstream || '',
        oid: oid || '',
      };
    });

export const parseBranchList = (raw) =>
  new Set(
    String(raw || '')
      .split('\n')
      .map((line) => line.trim())
      .filter(Boolean),
  );

export const isProtected = (name) =>
  PROTECTED_EXACT.has(name) || PROTECTED_PREFIXES.some((prefix) => name.startsWith(prefix));

const formatList = (items, formatter) => items.map((item) => `  - ${formatter(item)}`).join('\n');

export const markdownSection = (title, items, top, formatter) => {
  if (items.length === 0) {
    return `### ${title}\n\n- (none)\n`;
  }
  const visible = items.slice(0, top);
  const tail = items.length > top ? `\n- ... and ${items.length - top} more\n` : '';
  return `### ${title}\n\n${formatList(visible, formatter)}${tail}\n`;
};

export const deriveGhPrBaseBranch = (baseRef, remoteName) => {
  const value = String(baseRef || '').trim();
  if (!value) return '';
  if (value.startsWith('refs/heads/')) {
    return value.slice('refs/heads/'.length);
  }
  const remotePrefix = `refs/remotes/${remoteName}/`;
  if (value.startsWith(remotePrefix)) {
    return value.slice(remotePrefix.length);
  }
  if (value.startsWith(`${remoteName}/`)) {
    return value.slice(remoteName.length + 1);
  }
  return value;
};

const groupMergedPrsByHeadRefName = (items) => {
  const byBranch = new Map();
  for (const item of items) {
    const current = byBranch.get(item.headRefName) || [];
    current.push(item);
    current.sort((a, b) => String(b.mergedAt || '').localeCompare(String(a.mergedAt || '')));
    byBranch.set(item.headRefName, current);
  }
  return byBranch;
};

export const loadMergedPullRequests = (
  {
    limit = DEFAULT_GH_PR_LIMIT,
    baseBranch = DEFAULT_GH_PR_BASE,
  } = {},
  { ghRunner = runGhSafe } = {},
) => {
  const args = [
    'pr',
    'list',
    '--state',
    'merged',
    '--limit',
    String(limit),
    '--json',
    'number,title,url,mergedAt,headRefName,headRefOid,baseRefName',
  ];
  if (baseBranch) {
    args.splice(6, 0, '--base', baseBranch);
  }

  const result = ghRunner(args);

  if (!result.ok) {
    return {
      available: false,
      reason: result.message || result.output || 'gh unavailable',
      requestedBaseBranch: baseBranch,
      requestedLimit: limit,
      items: [],
      byHeadRefName: new Map(),
    };
  }

  const items = JSON.parse(result.output || '[]')
    .filter((item) => item && item.headRefName && item.headRefOid)
    .filter((item) => !baseBranch || item.baseRefName === baseBranch)
    .map((item) => ({
      number: item.number,
      title: item.title || '',
      url: item.url || '',
      mergedAt: item.mergedAt || '',
      headRefName: item.headRefName,
      headRefOid: item.headRefOid,
      baseRefName: item.baseRefName || '',
    }));

  return {
    available: true,
    reason: '',
    requestedBaseBranch: baseBranch,
    requestedLimit: limit,
    items,
    byHeadRefName: groupMergedPrsByHeadRefName(items),
  };
};

const defaultWorktreeStatus = (worktreePath) => runGitSafe(['-C', worktreePath, 'status', '--short']);
const defaultCommitOnBase = (commit, baseRef) => runGitSafe(['merge-base', '--is-ancestor', commit, baseRef]).ok;

export const collectWorktreeInventory = (
  worktrees,
  { currentWorktreePath, baseRef },
  {
    getStatus = defaultWorktreeStatus,
    isCommitOnBase = defaultCommitOnBase,
  } = {},
) => {
  const linkedBranches = [];
  const detachedOnBaseClean = [];
  const skippedDetached = [];

  for (const worktree of worktrees) {
    if (worktree.path === currentWorktreePath) continue;

    if (worktree.branch) {
      linkedBranches.push({
        path: worktree.path,
        branch: worktree.branch,
      });
      continue;
    }

    if (!worktree.detached) {
      skippedDetached.push({
        path: worktree.path,
        head: worktree.head || '',
        reason: 'no-branch',
      });
      continue;
    }
    if (worktree.locked) {
      skippedDetached.push({
        path: worktree.path,
        head: worktree.head || '',
        reason: 'locked-worktree',
      });
      continue;
    }
    if (worktree.prunable) {
      skippedDetached.push({
        path: worktree.path,
        head: worktree.head || '',
        reason: 'prunable-worktree',
      });
      continue;
    }

    const status = getStatus(worktree.path);
    if (!status.ok) {
      skippedDetached.push({
        path: worktree.path,
        head: worktree.head || '',
        reason: 'status-unavailable',
      });
      continue;
    }
    if (String(status.output || '').trim()) {
      skippedDetached.push({
        path: worktree.path,
        head: worktree.head || '',
        reason: 'dirty-worktree',
      });
      continue;
    }
    if (!worktree.head || !isCommitOnBase(worktree.head, baseRef)) {
      skippedDetached.push({
        path: worktree.path,
        head: worktree.head || '',
        reason: 'head-not-on-base',
      });
      continue;
    }

    detachedOnBaseClean.push({
      path: worktree.path,
      head: worktree.head,
    });
  }

  linkedBranches.sort((a, b) => a.branch.localeCompare(b.branch));
  detachedOnBaseClean.sort((a, b) => a.path.localeCompare(b.path));
  skippedDetached.sort((a, b) => a.path.localeCompare(b.path));

  return {
    linkedBranches,
    detachedOnBaseClean,
    skippedDetached,
  };
};

export const collectLocalPrMergedCandidates = (
  localRefs,
  {
    currentBranch,
    mergedLocal,
    linkedWorktreeBranches,
  },
  {
    mergedPullRequests,
  },
) => {
  const linkedBranchSet = new Set(linkedWorktreeBranches.map((item) => item.branch));

  return localRefs
    .filter((ref) => !mergedLocal.has(ref.name))
    .filter((ref) => ref.name !== currentBranch)
    .filter((ref) => !isProtected(ref.name))
    .filter((ref) => !linkedBranchSet.has(ref.name))
    .map((ref) => {
      const candidates = mergedPullRequests.byHeadRefName.get(ref.name) || [];
      const pr = candidates.find((item) => item.headRefOid === ref.oid);
      if (!pr) return null;
      return {
        branch: ref.name,
        number: pr.number,
        mergedAt: pr.mergedAt,
        url: pr.url,
        headRefOid: pr.headRefOid,
      };
    })
    .filter(Boolean)
    .sort((a, b) => String(b.mergedAt || '').localeCompare(String(a.mergedAt || '')));
};

export const buildInventoryReport = (
  options,
  {
    nowUnix = Math.floor(Date.now() / 1000),
    generatedAt = new Date().toISOString(),
    gitRunner = runGit,
    mergedPullRequestsLoader = loadMergedPullRequests,
  } = {},
) => {
  const currentBranch = gitRunner(['branch', '--show-current']);
  const currentWorktreePath = gitRunner(['rev-parse', '--show-toplevel']);

  const localRefRaw = gitRunner([
    'for-each-ref',
    'refs/heads',
    '--format=%(refname:short)\t%(committerdate:iso8601)\t%(committerdate:unix)\t%(upstream:short)\t%(objectname)',
  ]);
  const remoteRefRaw = gitRunner([
    'for-each-ref',
    `refs/remotes/${options.remote}`,
    '--format=%(refname:short)\t%(committerdate:iso8601)\t%(committerdate:unix)\t%(upstream:short)\t%(objectname)',
  ]);
  const worktreeRaw = gitRunner(['worktree', 'list', '--porcelain']);

  const mergedLocalRaw = gitRunner(['branch', '--format=%(refname:short)', '--merged', options.base]);
  const mergedRemoteRaw = gitRunner(['branch', '-r', '--format=%(refname:short)', '--merged', options.base]);

  const localRefs = parseRefs(localRefRaw, options.remote);
  const remoteRefs = parseRefs(remoteRefRaw, options.remote).filter(
    (ref) => ref.name !== options.remote && ref.name !== `${options.remote}/HEAD`,
  );
  const parsedWorktrees = parseWorktreePorcelain(worktreeRaw);
  const mergedLocal = parseBranchList(mergedLocalRaw);
  const mergedRemote = parseBranchList(mergedRemoteRaw);
  const ghPrBaseBranch = options.ghPrBase || deriveGhPrBaseBranch(options.base, options.remote);
  const mergedPullRequests = mergedPullRequestsLoader({
    limit: options.ghPrLimit,
    baseBranch: ghPrBaseBranch,
  });

  const localMergedCandidates = localRefs
    .filter((ref) => mergedLocal.has(ref.name))
    .map((ref) => ref.name)
    .filter((name) => name !== currentBranch && !isProtected(name))
    .sort();

  const remoteMergedCandidates = remoteRefs
    .filter((ref) => mergedRemote.has(ref.name))
    .map((ref) => ref.shortName)
    .filter((name) => name !== 'HEAD' && !isProtected(name))
    .sort();

  const remoteStaleCandidates = remoteRefs
    .filter((ref) => !mergedRemote.has(ref.name))
    .map((ref) => ({
      branch: ref.shortName,
      ageDays: Math.floor((nowUnix - ref.dateUnix) / 86400),
    }))
    .filter((item) => item.ageDays >= options.staleDays)
    .filter((item) => !isProtected(item.branch))
    .sort((a, b) => b.ageDays - a.ageDays);

  const worktreeInventory = collectWorktreeInventory(parsedWorktrees, {
    currentWorktreePath,
    baseRef: options.base,
  });

  const localPrMergedCandidates = mergedPullRequests.available
    ? collectLocalPrMergedCandidates(
        localRefs,
        {
          currentBranch,
          mergedLocal,
          linkedWorktreeBranches: worktreeInventory.linkedBranches,
        },
        {
          mergedPullRequests,
        },
      )
    : [];

  return {
    generatedAt,
    base: options.base,
    remote: options.remote,
    currentBranch,
    currentWorktreePath,
    protectedRules: {
      exact: Array.from(PROTECTED_EXACT),
      prefixes: PROTECTED_PREFIXES,
    },
    ghMergedPullRequests: {
      available: mergedPullRequests.available,
      reason: mergedPullRequests.reason,
      requestedBaseBranch: mergedPullRequests.requestedBaseBranch,
      requestedLimit: mergedPullRequests.requestedLimit,
      matched: mergedPullRequests.items.length,
    },
    counts: {
      local: localRefs.length,
      remote: remoteRefs.length,
      localMerged: mergedLocal.size,
      remoteMerged: mergedRemote.size,
      localMergedCandidates: localMergedCandidates.length,
      localPrMergedCandidates: localPrMergedCandidates.length,
      linkedWorktreeBranches: worktreeInventory.linkedBranches.length,
      detachedWorktreesOnBaseClean: worktreeInventory.detachedOnBaseClean.length,
      remoteMergedCandidates: remoteMergedCandidates.length,
      remoteStaleCandidates: remoteStaleCandidates.length,
    },
    candidates: {
      localMerged: localMergedCandidates,
      localPrMergedManualReview: localPrMergedCandidates,
      linkedWorktreeBranches: worktreeInventory.linkedBranches,
      detachedWorktreesOnBaseClean: worktreeInventory.detachedOnBaseClean,
      remoteMerged: remoteMergedCandidates,
      remoteStaleByAge: remoteStaleCandidates,
    },
    skipped: {
      detachedWorktrees: worktreeInventory.skippedDetached,
    },
  };
};

export const renderMarkdown = (report, options) => {
  const remoteStaleDisplay = report.candidates.remoteStaleByAge.map(
    (item) => `${item.branch} (${item.ageDays}d)`,
  );

  return `# Branch Inventory Report

- generatedAt: ${report.generatedAt}
- base: \`${report.base}\`
- remote: \`${report.remote}\`
- currentBranch: \`${report.currentBranch}\`
- currentWorktreePath: \`${report.currentWorktreePath}\`
- gh merged PR lookup: ${
    report.ghMergedPullRequests.available
      ? `enabled (base=${report.ghMergedPullRequests.requestedBaseBranch || 'none'}, limit=${report.ghMergedPullRequests.requestedLimit}, matched=${report.ghMergedPullRequests.matched})`
      : `unavailable (${report.ghMergedPullRequests.reason})`
  }

## Counts

- local branches: ${report.counts.local}
- remote branches: ${report.counts.remote}
- local merged (raw): ${report.counts.localMerged}
- remote merged (raw): ${report.counts.remoteMerged}
- local merged candidates (safe-delete): ${report.counts.localMergedCandidates}
- local PR-merged candidates (manual review): ${report.counts.localPrMergedCandidates}
- linked worktree branches (excluded): ${report.counts.linkedWorktreeBranches}
- detached worktrees on base, clean (manual review): ${report.counts.detachedWorktreesOnBaseClean}
- remote merged candidates (safe-delete): ${report.counts.remoteMergedCandidates}
- remote stale candidates by age >= ${options.staleDays}d: ${report.counts.remoteStaleCandidates}

${markdownSection('Local merged candidates (safe-delete)', report.candidates.localMerged, options.top, (item) => `\`${item}\``)}
${markdownSection(
  'Local PR-merged candidates (manual review only)',
  report.candidates.localPrMergedManualReview,
  options.top,
  (item) => `\`${item.branch}\` (#${item.number})`,
)}
${markdownSection(
  'Linked worktree branches (excluded from cleanup)',
  report.candidates.linkedWorktreeBranches,
  options.top,
  (item) => `\`${item.branch}\` @ \`${item.path}\``,
)}
${markdownSection(
  'Detached clean worktrees whose HEAD is on base (manual review only)',
  report.candidates.detachedWorktreesOnBaseClean,
  options.top,
  (item) => `\`${item.path}\` @ \`${item.head.slice(0, 12)}\``,
)}
${markdownSection('Remote merged candidates (safe-delete)', report.candidates.remoteMerged, options.top, (item) => `\`${item}\``)}
${markdownSection(
  `Remote stale candidates by age (>=${options.staleDays}d, not merged)`,
  remoteStaleDisplay,
  options.top,
  (item) => `\`${item}\``,
)}
## Suggested next commands

\`\`\`bash
# Inventory only
pnpm run maintenance:branch:inventory

# Apply local merged cleanup (safe side, ancestry-merged only)
pnpm run maintenance:branch:cleanup:apply:local

# Detached worktrees / PR-merged local branches remain manual-review items
pnpm run maintenance:worktree:cleanup:dry-run
\`\`\`
`;
};

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const report = buildInventoryReport(options);
  const markdown = renderMarkdown(report, options);

  const jsonPath = path.resolve(options.outputJson);
  const mdPath = path.resolve(options.outputMd);
  fs.mkdirSync(path.dirname(jsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(mdPath), { recursive: true });
  fs.writeFileSync(jsonPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
  fs.writeFileSync(mdPath, markdown, 'utf8');

  console.log(`[branch-inventory] wrote ${jsonPath}`);
  console.log(`[branch-inventory] wrote ${mdPath}`);
  console.log(
    `[branch-inventory] local=${report.counts.local} remote=${report.counts.remote} localMergedCandidates=${report.counts.localMergedCandidates} localPrMergedCandidates=${report.counts.localPrMergedCandidates} remoteMergedCandidates=${report.counts.remoteMergedCandidates}`,
  );
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error(`[branch-inventory] ${error instanceof Error ? error.message : String(error)}`);
    process.exit(1);
  }
}
