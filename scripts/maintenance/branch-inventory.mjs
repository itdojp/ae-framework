#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

const DEFAULT_BASE_REF = 'origin/main';
const DEFAULT_REMOTE = 'origin';
const DEFAULT_OUTPUT_JSON = 'artifacts/maintenance/branch-inventory.json';
const DEFAULT_OUTPUT_MD = 'artifacts/maintenance/branch-inventory.md';
const DEFAULT_STALE_DAYS = 90;
const DEFAULT_TOP = 30;

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
  --top <n>            Number of branch names to print in markdown sections (default: ${DEFAULT_TOP})
  --help               Show this help
`);
};

const parseArgs = (argv) => {
  const options = {
    base: DEFAULT_BASE_REF,
    remote: DEFAULT_REMOTE,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    staleDays: DEFAULT_STALE_DAYS,
    top: DEFAULT_TOP,
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
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.base) {
    throw new Error('--base is required');
  }
  if (!options.remote) {
    throw new Error('--remote is required');
  }
  if (!Number.isInteger(options.staleDays) || options.staleDays < 1) {
    throw new Error('--stale-days must be a positive integer');
  }
  if (!Number.isInteger(options.top) || options.top < 1) {
    throw new Error('--top must be a positive integer');
  }
  return options;
};

const runGit = (args) =>
  execFileSync('git', args, {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  }).trimEnd();

const parseRefs = (raw, remoteName) =>
  raw
    .split('\n')
    .map((line) => line.trim())
    .filter(Boolean)
    .map((line) => {
      const [name, dateIso, dateUnixRaw, upstream] = line.split('\t');
      const dateUnix = Number(dateUnixRaw || 0);
      const shortName = name.startsWith(`${remoteName}/`) ? name.slice(remoteName.length + 1) : name;
      return {
        name,
        shortName,
        dateIso,
        dateUnix: Number.isFinite(dateUnix) ? dateUnix : 0,
        upstream: upstream || '',
      };
    });

const parseBranchList = (raw) =>
  new Set(
    raw
      .split('\n')
      .map((line) => line.trim())
      .filter(Boolean),
  );

const isProtected = (name) =>
  PROTECTED_EXACT.has(name) || PROTECTED_PREFIXES.some((prefix) => name.startsWith(prefix));

const formatList = (branches) => branches.map((branch) => `  - \`${branch}\``).join('\n');

const markdownSection = (title, branches, top) => {
  if (branches.length === 0) {
    return `### ${title}\n\n- (none)\n`;
  }
  const items = branches.slice(0, top);
  return `### ${title}\n\n${formatList(items)}\n${branches.length > top ? `\n- ... and ${branches.length - top} more\n` : ''}`;
};

try {
  const options = parseArgs(process.argv.slice(2));
  const now = Math.floor(Date.now() / 1000);
  const generatedAt = new Date().toISOString();
  const currentBranch = runGit(['branch', '--show-current']);

  const localRefRaw = runGit([
    'for-each-ref',
    'refs/heads',
    '--format=%(refname:short)\t%(committerdate:iso8601)\t%(committerdate:unix)\t%(upstream:short)',
  ]);
  const remoteRefRaw = runGit([
    'for-each-ref',
    `refs/remotes/${options.remote}`,
    '--format=%(refname:short)\t%(committerdate:iso8601)\t%(committerdate:unix)\t%(upstream:short)',
  ]);

  const mergedLocalRaw = runGit(['branch', '--format=%(refname:short)', '--merged', options.base]);
  const mergedRemoteRaw = runGit(['branch', '-r', '--format=%(refname:short)', '--merged', options.base]);

  const localRefs = parseRefs(localRefRaw, options.remote);
  const remoteRefs = parseRefs(remoteRefRaw, options.remote).filter(
    (ref) => ref.name !== `${options.remote}/HEAD`,
  );

  const mergedLocal = parseBranchList(mergedLocalRaw);
  const mergedRemote = parseBranchList(mergedRemoteRaw);

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
      ageDays: Math.floor((now - ref.dateUnix) / 86400),
    }))
    .filter((item) => item.ageDays >= options.staleDays)
    .filter((item) => !isProtected(item.branch))
    .sort((a, b) => b.ageDays - a.ageDays)
    .map((item) => `${item.branch} (${item.ageDays}d)`);

  const report = {
    generatedAt,
    base: options.base,
    remote: options.remote,
    currentBranch,
    protectedRules: {
      exact: Array.from(PROTECTED_EXACT),
      prefixes: PROTECTED_PREFIXES,
    },
    counts: {
      local: localRefs.length,
      remote: remoteRefs.length,
      localMerged: mergedLocal.size,
      remoteMerged: mergedRemote.size,
      localMergedCandidates: localMergedCandidates.length,
      remoteMergedCandidates: remoteMergedCandidates.length,
      remoteStaleCandidates: remoteStaleCandidates.length,
    },
    candidates: {
      localMerged: localMergedCandidates,
      remoteMerged: remoteMergedCandidates,
      remoteStaleByAge: remoteStaleCandidates,
    },
  };

  const markdown = `# Branch Inventory Report

- generatedAt: ${generatedAt}
- base: \`${options.base}\`
- remote: \`${options.remote}\`
- currentBranch: \`${currentBranch}\`

## Counts

- local branches: ${report.counts.local}
- remote branches: ${report.counts.remote}
- local merged (raw): ${report.counts.localMerged}
- remote merged (raw): ${report.counts.remoteMerged}
- local merged candidates (safe-delete): ${report.counts.localMergedCandidates}
- remote merged candidates (safe-delete): ${report.counts.remoteMergedCandidates}
- remote stale candidates by age >= ${options.staleDays}d: ${report.counts.remoteStaleCandidates}

${markdownSection('Local merged candidates (safe-delete)', localMergedCandidates, options.top)}
${markdownSection('Remote merged candidates (safe-delete)', remoteMergedCandidates, options.top)}
${markdownSection(
  `Remote stale candidates by age (>=${options.staleDays}d, not merged)`,
  remoteStaleCandidates,
  options.top,
)}
## Suggested next commands

\`\`\`bash
# Dry-run (list only)
pnpm run maintenance:branch:cleanup:dry-run

# Apply local merged cleanup (safe side)
pnpm run maintenance:branch:cleanup:apply:local
\`\`\`
`;

  const jsonPath = path.resolve(options.outputJson);
  const mdPath = path.resolve(options.outputMd);
  fs.mkdirSync(path.dirname(jsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(mdPath), { recursive: true });
  fs.writeFileSync(jsonPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
  fs.writeFileSync(mdPath, markdown, 'utf8');

  console.log(`[branch-inventory] wrote ${jsonPath}`);
  console.log(`[branch-inventory] wrote ${mdPath}`);
  console.log(
    `[branch-inventory] local=${report.counts.local} remote=${report.counts.remote} localMergedCandidates=${report.counts.localMergedCandidates} remoteMergedCandidates=${report.counts.remoteMergedCandidates}`,
  );
} catch (error) {
  console.error(`[branch-inventory] ${error instanceof Error ? error.message : String(error)}`);
  process.exit(1);
}
