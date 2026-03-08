#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { refreshRemoteTrackingRefs } from './git-remote-refresh.mjs';

const DEFAULT_BASE_REF = 'origin/main';
const DEFAULT_REMOTE = 'origin';
const DEFAULT_SCOPE = 'local';
const DEFAULT_MAX = 200;
const DEFAULT_OUTPUT_JSON = 'tmp/maintenance/branch-cleanup-report.json';
const DEFAULT_REMOTE_MANIFEST_MODE = 'merged';

const PROTECTED_EXACT = new Set(['main', 'master', 'develop', 'staging']);
const PROTECTED_PREFIXES = ['release/', 'hotfix/'];
const REMOTE_MANIFEST_MODES = new Set(['merged', 'stale-delete']);

const readRequiredValue = (argv, index, flag) => {
  const next = argv[index + 1];
  const value = String(next || '').trim();
  if (!value || value.startsWith('--')) {
    throw new Error(`${flag} requires a non-empty value`);
  }
  return value;
};

const usage = () => {
  console.log(`Usage: node scripts/maintenance/branch-cleanup.mjs [options]

Options:
  --base <ref>                  Base ref to compare merge status (default: ${DEFAULT_BASE_REF})
  --remote <name>               Remote name (default: ${DEFAULT_REMOTE})
  --scope <mode>                local | remote | both (default: ${DEFAULT_SCOPE})
  --max <n>                     Max branches to process per scope (default: ${DEFAULT_MAX})
  --output-json <path>          JSON output path (default: ${DEFAULT_OUTPUT_JSON})
  --remote-manifest-json <path> Use remote-branch-triage JSON as reviewed delete manifest
  --remote-manifest-mode <mode> merged | stale-delete (default: ${DEFAULT_REMOTE_MANIFEST_MODE})
  --remote-branches-file <path> Use explicit approved branch list (text, JSON array, or { branches: [...] })
  --fetch                       Run 'git fetch --prune <remote>' before analysis
  --apply                       Execute deletion (without this, dry-run only)
  --help                        Show this help
`);
};

export const parseArgs = (argv) => {
  const options = {
    base: DEFAULT_BASE_REF,
    remote: DEFAULT_REMOTE,
    scope: DEFAULT_SCOPE,
    max: DEFAULT_MAX,
    outputJson: DEFAULT_OUTPUT_JSON,
    remoteManifestJson: '',
    remoteManifestJsonProvided: false,
    remoteManifestMode: DEFAULT_REMOTE_MANIFEST_MODE,
    remoteManifestModeProvided: false,
    remoteBranchesFile: '',
    remoteBranchesFileProvided: false,
    fetch: false,
    apply: false,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--base') {
      options.base = readRequiredValue(argv, i, '--base');
      i += 1;
      continue;
    }
    if (arg === '--remote') {
      options.remote = readRequiredValue(argv, i, '--remote');
      i += 1;
      continue;
    }
    if (arg === '--scope') {
      options.scope = readRequiredValue(argv, i, '--scope');
      i += 1;
      continue;
    }
    if (arg === '--max') {
      options.max = Number(argv[++i]);
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = readRequiredValue(argv, i, '--output-json');
      i += 1;
      continue;
    }
    if (arg === '--remote-manifest-json') {
      options.remoteManifestJson = readRequiredValue(argv, i, '--remote-manifest-json');
      options.remoteManifestJsonProvided = true;
      i += 1;
      continue;
    }
    if (arg === '--remote-manifest-mode') {
      options.remoteManifestMode = readRequiredValue(argv, i, '--remote-manifest-mode');
      options.remoteManifestModeProvided = true;
      i += 1;
      continue;
    }
    if (arg === '--remote-branches-file') {
      options.remoteBranchesFile = readRequiredValue(argv, i, '--remote-branches-file');
      options.remoteBranchesFileProvided = true;
      i += 1;
      continue;
    }
    if (arg === '--fetch') {
      options.fetch = true;
      continue;
    }
    if (arg === '--apply') {
      options.apply = true;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.base) throw new Error('--base is required');
  if (!options.remote) throw new Error('--remote is required');
  if (!['local', 'remote', 'both'].includes(options.scope)) {
    throw new Error('--scope must be local, remote, or both');
  }
  if (!Number.isInteger(options.max) || options.max < 1) {
    throw new Error('--max must be a positive integer');
  }
  if (options.remoteManifestJson && options.remoteBranchesFile) {
    throw new Error('--remote-manifest-json and --remote-branches-file are mutually exclusive');
  }
  if (!REMOTE_MANIFEST_MODES.has(options.remoteManifestMode)) {
    throw new Error('--remote-manifest-mode must be merged or stale-delete');
  }
  if (options.remoteManifestModeProvided && !options.remoteManifestJsonProvided) {
    throw new Error('--remote-manifest-mode requires --remote-manifest-json');
  }
  if ((options.remoteManifestJson || options.remoteBranchesFile) && options.scope === 'local') {
    throw new Error('remote reviewed input cannot be used with --scope local');
  }
  return options;
};

const runGit = (args) =>
  execFileSync('git', args, {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  }).trimEnd();

const runGitSafe = (args) => {
  try {
    const stdout = execFileSync('git', args, {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    return { ok: true, output: stdout.trimEnd() };
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

const isProtected = (name) =>
  PROTECTED_EXACT.has(name) || PROTECTED_PREFIXES.some((prefix) => name.startsWith(prefix));

const parseBranchList = (raw) =>
  raw
    .split('\n')
    .map((line) => line.trim())
    .filter(Boolean);

const normalizeRemoteEntry = (item, selectionMode) => {
  if (typeof item === 'string') {
    const branch = item.trim();
    if (!branch) throw new Error('Remote branch entry must not be empty');
    return {
      branch,
      branchOid: '',
      selectionMode,
      source: selectionMode,
    };
  }
  if (!item || typeof item !== 'object') {
    throw new Error('Remote branch entry must be a string or an object');
  }
  const branch = String(item.branch || '').trim();
  if (!branch) throw new Error('Remote branch entry requires branch');
  return {
    branch,
    branchOid: typeof item.branchOid === 'string' ? item.branchOid.trim() : '',
    selectionMode,
    source: selectionMode,
    deleteCommand: typeof item.deleteCommand === 'string' ? item.deleteCommand : '',
    decision: typeof item.decision === 'string' ? item.decision : '',
    prState: typeof item.prState === 'string' ? item.prState : '',
  };
};

export const parseRemoteBranchesFile = (raw) => {
  const trimmed = raw.trim();
  if (!trimmed) return [];
  if (trimmed.startsWith('[') || trimmed.startsWith('{')) {
    const parsed = JSON.parse(trimmed);
    if (Array.isArray(parsed)) {
      return parsed.map((item) => normalizeRemoteEntry(item, 'branch-list'));
    }
    if (parsed && typeof parsed === 'object' && Array.isArray(parsed.branches)) {
      return parsed.branches.map((item) => normalizeRemoteEntry(item, 'branch-list'));
    }
    throw new Error('JSON branch list must be an array or an object with branches');
  }
  return trimmed
    .split('\n')
    .map((line) => line.trim())
    .filter((line) => line && !line.startsWith('#'))
    .map((line) => normalizeRemoteEntry(line, 'branch-list'));
};

export const selectRemoteCandidatesFromTriage = (report, mode) => {
  if (mode === 'merged') {
    return (Array.isArray(report?.remoteMerged) ? report.remoteMerged : []).map((item) =>
      normalizeRemoteEntry(item, 'triage-merged'),
    );
  }
  if (mode === 'stale-delete') {
    return (Array.isArray(report?.remoteStale) ? report.remoteStale : [])
      .filter((item) => item && item.decision === 'delete')
      .map((item) => normalizeRemoteEntry(item, 'triage-stale-delete'));
  }
  throw new Error(`Unsupported remote manifest mode: ${mode}`);
};

const loadRemoteSelection = (options) => {
  if (options.remoteManifestJson) {
    const manifestPath = path.resolve(options.remoteManifestJson);
    const report = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
    const manifestRemote =
      report?.sourceInventory?.remote || report?.remoteName || report?.githubPullRequests?.remote || '';
    const manifestBase = report?.sourceInventory?.base || report?.base || '';
    if (!manifestRemote || !manifestBase) {
      throw new Error(
        'remote manifest is missing sourceInventory.remote/base (or compatible fields); cannot use for remote cleanup',
      );
    }
    if (manifestRemote !== options.remote) {
      throw new Error(
        `remote manifest remote mismatch: expected ${options.remote}, got ${manifestRemote}`,
      );
    }
    if (manifestBase !== options.base) {
      throw new Error(`remote manifest base mismatch: expected ${options.base}, got ${manifestBase}`);
    }
    return {
      mode: options.remoteManifestMode === 'merged' ? 'triage-merged' : 'triage-stale-delete',
      sourcePath: manifestPath,
      expectedBase: options.base,
      expectedRemote: options.remote,
      entries: selectRemoteCandidatesFromTriage(report, options.remoteManifestMode),
    };
  }

  if (options.remoteBranchesFile) {
    const branchFilePath = path.resolve(options.remoteBranchesFile);
    return {
      mode: 'branch-list',
      sourcePath: branchFilePath,
      expectedBase: '',
      expectedRemote: '',
      entries: parseRemoteBranchesFile(fs.readFileSync(branchFilePath, 'utf8')),
    };
  }

  return {
    mode: 'inventory-merged',
    sourcePath: '',
    expectedBase: '',
    expectedRemote: options.remote,
    entries: [],
  };
};

const parseRemoteRefOids = (raw, remoteName) => {
  const map = new Map();
  for (const line of raw.split('\n').map((item) => item.trim()).filter(Boolean)) {
    const [ref, oid] = line.split(/\s+/, 2);
    if (!ref || !oid) continue;
    if (!ref.startsWith(`${remoteName}/`)) continue;
    if (ref === `${remoteName}/HEAD`) continue;
    map.set(ref.slice(remoteName.length + 1), oid);
  }
  return map;
};

export const collectRemoteCleanupPlan = ({
  entries,
  remoteName,
  mergedRemoteRefs,
  remoteRefOids,
  max,
  selectionMode,
  sourcePath = '',
  expectedBase = '',
  expectedRemote = '',
}) => {
  const plannedDetailed = [];
  const blocked = [];

  for (const entry of entries) {
    const branch = entry.branch;
    if (isProtected(branch)) {
      blocked.push({ branch, reason: 'protected-branch' });
      continue;
    }

    const actualOid = remoteRefOids.get(branch);
    if (!actualOid) {
      blocked.push({ branch, reason: 'remote-ref-missing', expectedOid: entry.branchOid || '' });
      continue;
    }

    if (entry.branchOid && entry.branchOid !== actualOid) {
      blocked.push({
        branch,
        reason: 'oid-mismatch',
        expectedOid: entry.branchOid,
        actualOid,
      });
      continue;
    }

    if ((selectionMode === 'inventory-merged' || selectionMode === 'triage-merged') &&
        !mergedRemoteRefs.has(`${remoteName}/${branch}`)) {
      blocked.push({ branch, reason: 'not-merged-to-base', actualOid });
      continue;
    }

    plannedDetailed.push({
      branch,
      branchOid: entry.branchOid || '',
      actualOid,
      selectionMode,
      deleteCommand: `git push ${remoteName} --delete ${branch}`,
    });
  }

  return {
    selection: {
      mode: selectionMode,
      sourcePath,
      expectedBase,
      expectedRemote,
    },
    totalCandidates: entries.length,
    planned: plannedDetailed.slice(0, max).map((item) => item.branch),
    plannedDetailed: plannedDetailed.slice(0, max),
    blocked,
    considered: [],
    deleted: [],
    failed: [],
  };
};

const buildInventoryRemoteEntries = (options, mergedRemoteRefs) =>
  Array.from(mergedRemoteRefs)
    .filter((name) => name.startsWith(`${options.remote}/`))
    .filter((name) => name !== `${options.remote}/HEAD`)
    .map((name) => name.slice(options.remote.length + 1))
    .sort()
    .map((branch) => normalizeRemoteEntry(branch, 'inventory-merged'));

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const generatedAt = new Date().toISOString();
  const currentBranch = runGit(['branch', '--show-current']);
  const shouldLocal = options.scope === 'local' || options.scope === 'both';
  const shouldRemote = options.scope === 'remote' || options.scope === 'both';
  const fetch = options.fetch
    ? refreshRemoteTrackingRefs(options.remote, { gitRunner: runGitSafe })
    : {
        attempted: false,
        ok: true,
        remote: options.remote,
        output: '',
      };

  const mergedLocal = new Set(
    parseBranchList(runGit(['branch', '--format=%(refname:short)', '--merged', options.base])),
  );
  const mergedRemoteRefs = new Set(
    parseBranchList(runGit(['branch', '-r', '--format=%(refname:short)', '--merged', options.base])),
  );
  const remoteRefOids = parseRemoteRefOids(
    runGit(['for-each-ref', '--format=%(refname:short) %(objectname)', `refs/remotes/${options.remote}`]),
    options.remote,
  );

  const localCandidates = shouldLocal
    ? parseBranchList(runGit(['branch', '--format=%(refname:short)']))
        .filter((name) => mergedLocal.has(name))
        .filter((name) => name !== currentBranch)
        .filter((name) => !isProtected(name))
        .sort()
    : [];

  const remoteSelection = shouldRemote ? loadRemoteSelection(options) : null;
  const selectedRemoteEntries =
    shouldRemote && remoteSelection
      ? remoteSelection.mode === 'inventory-merged'
        ? buildInventoryRemoteEntries(options, mergedRemoteRefs)
        : remoteSelection.entries
      : [];

  const localResult = {
    totalCandidates: localCandidates.length,
    planned: localCandidates.slice(0, options.max),
    considered: [],
    deleted: [],
    failed: [],
  };
  const remoteResult = shouldRemote
    ? collectRemoteCleanupPlan({
        entries: selectedRemoteEntries,
        remoteName: options.remote,
        mergedRemoteRefs,
        remoteRefOids,
        max: options.max,
        selectionMode: remoteSelection.mode,
        sourcePath: remoteSelection.sourcePath,
        expectedBase: remoteSelection.expectedBase,
        expectedRemote: remoteSelection.expectedRemote,
      })
    : {
        selection: {
          mode: 'disabled',
          sourcePath: '',
        },
        totalCandidates: 0,
        planned: [],
        plannedDetailed: [],
        blocked: [],
        considered: [],
        deleted: [],
        failed: [],
      };

  if (options.apply && shouldLocal) {
    for (const branch of localCandidates) {
      if (localResult.deleted.length >= options.max) break;
      localResult.considered.push(branch);
      const result = runGitSafe(['branch', '-d', branch]);
      if (result.ok) {
        localResult.deleted.push(branch);
      } else {
        localResult.failed.push({ branch, reason: result.message || result.output });
      }
    }
  }

  if (options.apply && shouldRemote) {
    for (const item of remoteResult.plannedDetailed) {
      if (remoteResult.deleted.length >= options.max) break;
      remoteResult.considered.push(item.branch);
      const result = runGitSafe(['push', options.remote, '--delete', item.branch]);
      if (result.ok) {
        remoteResult.deleted.push(item.branch);
      } else {
        remoteResult.failed.push({ branch: item.branch, reason: result.message || result.output });
      }
    }
  }

  const report = {
    generatedAt,
    base: options.base,
    remoteName: options.remote,
    scope: options.scope,
    apply: options.apply,
    max: options.max,
    currentBranch,
    fetch,
    protectedRules: {
      exact: Array.from(PROTECTED_EXACT),
      prefixes: PROTECTED_PREFIXES,
    },
    local: localResult,
    remote: remoteResult,
  };

  const outputPath = path.resolve(options.outputJson);
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');

  console.log(`[branch-cleanup] mode=${options.apply ? 'apply' : 'dry-run'} scope=${options.scope}`);
  if (fetch.attempted) {
    console.log(`[branch-cleanup] fetch=ok remote=${fetch.remote}`);
  }
  console.log(
    `[branch-cleanup] local candidates=${localCandidates.length}, remote candidates=${remoteResult.totalCandidates}`,
  );
  if (shouldRemote) {
    console.log(
      `[branch-cleanup] remote selection=${remoteResult.selection.mode} blocked=${remoteResult.blocked.length}`,
    );
  }

  if (!options.apply) {
    if (shouldLocal) {
      for (const branch of localResult.planned) {
        console.log(`DRYRUN local: git branch -d ${branch}`);
      }
    }
    if (shouldRemote) {
      for (const item of remoteResult.plannedDetailed) {
        console.log(`DRYRUN remote: ${item.deleteCommand}`);
      }
    }
  } else {
    if (shouldLocal) {
      console.log(
        `[branch-cleanup] local deleted=${localResult.deleted.length} failed=${localResult.failed.length}`,
      );
    }
    if (shouldRemote) {
      console.log(
        `[branch-cleanup] remote deleted=${remoteResult.deleted.length} failed=${remoteResult.failed.length}`,
      );
    }
  }
  console.log(`[branch-cleanup] wrote ${outputPath}`);
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error(`[branch-cleanup] ${error instanceof Error ? error.message : String(error)}`);
    process.exit(1);
  }
}
