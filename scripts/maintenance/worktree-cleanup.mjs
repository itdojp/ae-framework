#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { deriveRemoteFromBaseRef, refreshRemoteTrackingRefs } from './git-remote-refresh.mjs';

const DEFAULT_BASE_REF = 'origin/main';
const DEFAULT_MAX = 50;
const DEFAULT_OUTPUT_JSON = 'tmp/maintenance/worktree-cleanup-report.json';

const PROTECTED_EXACT = new Set(['main', 'master', 'develop', 'staging']);
const PROTECTED_PREFIXES = ['release/', 'hotfix/'];

const usage = () => {
  console.log(`Usage: node scripts/maintenance/worktree-cleanup.mjs [options]

Options:
  --base <ref>          Base ref to compare merge status (default: ${DEFAULT_BASE_REF})
  --max <n>             Max worktrees to process (default: ${DEFAULT_MAX})
  --output-json <path>  JSON output path (default: ${DEFAULT_OUTPUT_JSON})
  --fetch               Run 'git fetch --prune <remote>' before analysis
  --apply               Execute deletion (without this, dry-run only)
  --prune               Run 'git worktree prune' before analysis
  --help                Show this help
`);
};

const parseArgs = (argv) => {
  const options = {
    base: DEFAULT_BASE_REF,
    max: DEFAULT_MAX,
    outputJson: DEFAULT_OUTPUT_JSON,
    fetch: false,
    apply: false,
    prune: false,
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
    if (arg === '--max') {
      options.max = Number(argv[++i]);
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = String(argv[++i] || '').trim();
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
    if (arg === '--prune') {
      options.prune = true;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.base) throw new Error('--base is required');
  if (!Number.isInteger(options.max) || options.max < 1) {
    throw new Error('--max must be a positive integer');
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
    const output = execFileSync('git', args, {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    return { ok: true, output: output.trimEnd() };
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

const trimReason = (value) => {
  const raw = String(value || '').trim();
  if (!raw) return '';
  if (raw.startsWith('(') && raw.endsWith(')')) return raw.slice(1, -1).trim();
  return raw;
};

export const parseWorktreePorcelain = (raw) => {
  const entries = [];
  let current = null;

  const pushCurrent = () => {
    if (!current) return;
    entries.push(current);
    current = null;
  };

  const lines = String(raw || '').split('\n');
  for (const line of lines) {
    if (!line.trim()) continue;
    if (line.startsWith('worktree ')) {
      pushCurrent();
      current = {
        path: line.slice('worktree '.length).trim(),
        head: '',
        branchRef: '',
        branch: '',
        detached: false,
        bare: false,
        locked: false,
        lockedReason: '',
        prunable: false,
        prunableReason: '',
      };
      continue;
    }
    if (!current) continue;

    if (line.startsWith('HEAD ')) {
      current.head = line.slice('HEAD '.length).trim();
      continue;
    }
    if (line.startsWith('branch ')) {
      const ref = line.slice('branch '.length).trim();
      current.branchRef = ref;
      current.branch = ref.startsWith('refs/heads/') ? ref.slice('refs/heads/'.length) : ref;
      continue;
    }
    if (line === 'detached') {
      current.detached = true;
      continue;
    }
    if (line === 'bare') {
      current.bare = true;
      continue;
    }
    if (line.startsWith('locked')) {
      current.locked = true;
      current.lockedReason = trimReason(line.slice('locked'.length));
      continue;
    }
    if (line.startsWith('prunable')) {
      current.prunable = true;
      current.prunableReason = trimReason(line.slice('prunable'.length));
    }
  }

  pushCurrent();
  return entries;
};

export const isProtectedBranch = (name) =>
  PROTECTED_EXACT.has(name) || PROTECTED_PREFIXES.some((prefix) => name.startsWith(prefix));

const defaultBranchExists = (branch) => runGitSafe(['show-ref', '--verify', '--quiet', `refs/heads/${branch}`]).ok;

// NOTE: This "merged" check only succeeds when the branch tip is an ancestor
// of base. Squash merges typically create a new commit on base, so squash-merged
// branches may still be treated as "branch-not-merged" by this default.
const defaultIsMergedToBase = (branch, base) => runGitSafe(['merge-base', '--is-ancestor', branch, base]).ok;

/**
 * Collect worktrees that are safe cleanup candidates.
 *
 * @param {Array<{
 *   path: string,
 *   branch?: string,
 *   locked?: boolean
 * }>} worktrees Parsed `git worktree list --porcelain` entries.
 * @param {{ currentWorktreePath: string, baseRef: string }} context
 * @param {{
 *   branchExists?: (branch: string) => boolean,
 *   isMergedToBase?: (branch: string, baseRef: string) => boolean
 * }} [overrides]
 * `isMergedToBase` defaults to merge-base ancestor semantics (non-squash merge
 * oriented). To treat squash-merged branches as merged, pass a custom
 * implementation via `overrides`.
 */
export const collectCleanupCandidates = (
  worktrees,
  { currentWorktreePath, baseRef },
  {
    branchExists = defaultBranchExists,
    isMergedToBase = defaultIsMergedToBase,
  } = {},
) => {
  const candidates = [];
  const skipped = [];

  for (const worktree of worktrees) {
    const recordSkip = (reason) => {
      skipped.push({
        path: worktree.path,
        branch: worktree.branch || null,
        reason,
      });
    };

    if (worktree.path === currentWorktreePath) {
      recordSkip('current-worktree');
      continue;
    }
    if (!worktree.branch) {
      recordSkip('no-branch');
      continue;
    }
    if (isProtectedBranch(worktree.branch)) {
      recordSkip('protected-branch');
      continue;
    }
    if (worktree.locked) {
      recordSkip('locked-worktree');
      continue;
    }
    if (!branchExists(worktree.branch)) {
      recordSkip('missing-branch-ref');
      continue;
    }
    if (!isMergedToBase(worktree.branch, baseRef)) {
      recordSkip('branch-not-merged');
      continue;
    }

    candidates.push({
      path: worktree.path,
      branch: worktree.branch,
    });
  }

  return { candidates, skipped };
};

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const generatedAt = new Date().toISOString();
  const currentWorktreePath = runGit(['rev-parse', '--show-toplevel']);
  const fetchRemote = options.fetch ? deriveRemoteFromBaseRef(options.base) : '';
  if (options.fetch && !fetchRemote) {
    throw new Error('--fetch requires a remote-tracking --base such as origin/main');
  }
  const fetch = options.fetch
    ? refreshRemoteTrackingRefs(fetchRemote, { gitRunner: runGitSafe })
    : {
        attempted: false,
        ok: true,
        remote: '',
        output: '',
        message: '',
      };
  if (fetch.attempted && !fetch.ok) {
    const report = {
      generatedAt,
      base: options.base,
      apply: options.apply,
      max: options.max,
      fetch,
      error: fetch.message,
      prune: { attempted: false, ok: true, output: '' },
      currentWorktreePath,
      counts: {
        total: 0,
        candidates: 0,
        planned: 0,
        skipped: 0,
        deleted: 0,
        failed: 0,
        prunable: 0,
        locked: 0,
      },
      planned: [],
      deleted: [],
      failed: [],
      skipped: [],
    };
    const outputPath = path.resolve(options.outputJson);
    fs.mkdirSync(path.dirname(outputPath), { recursive: true });
    fs.writeFileSync(outputPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
    console.log(`[worktree-cleanup] wrote ${outputPath}`);
    throw new Error(fetch.message || 'failed to refresh remote-tracking refs');
  }

  let pruneResult = { attempted: false, ok: true, output: '' };
  if (options.prune) {
    const pruned = runGitSafe(['worktree', 'prune']);
    pruneResult = {
      attempted: true,
      ok: pruned.ok,
      output: pruned.output,
    };
  }

  const parsedWorktrees = parseWorktreePorcelain(runGit(['worktree', 'list', '--porcelain']));
  const { candidates, skipped } = collectCleanupCandidates(parsedWorktrees, {
    currentWorktreePath,
    baseRef: options.base,
  });

  const planned = candidates.slice(0, options.max);
  const deleted = [];
  const failed = [];

  if (options.apply) {
    for (const item of planned) {
      const result = runGitSafe(['worktree', 'remove', item.path]);
      if (result.ok) {
        deleted.push(item);
      } else {
        failed.push({
          ...item,
          reason: result.message || result.output || 'failed to remove worktree',
        });
      }
    }
  }

  const report = {
    generatedAt,
    base: options.base,
    apply: options.apply,
    max: options.max,
    fetch,
    prune: pruneResult,
    currentWorktreePath,
    counts: {
      total: parsedWorktrees.length,
      candidates: candidates.length,
      planned: planned.length,
      skipped: skipped.length,
      deleted: deleted.length,
      failed: failed.length,
      prunable: parsedWorktrees.filter((item) => item.prunable).length,
      locked: parsedWorktrees.filter((item) => item.locked).length,
    },
    planned,
    deleted,
    failed,
    skipped,
  };

  const outputPath = path.resolve(options.outputJson);
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');

  console.log(`[worktree-cleanup] mode=${options.apply ? 'apply' : 'dry-run'} base=${options.base}`);
  if (fetch.attempted) {
    console.log(`[worktree-cleanup] fetch=ok remote=${fetch.remote}`);
  }
  console.log(
    `[worktree-cleanup] total=${report.counts.total} candidates=${report.counts.candidates} planned=${report.counts.planned} deleted=${report.counts.deleted} failed=${report.counts.failed}`,
  );
  if (options.prune) {
    console.log(`[worktree-cleanup] prune=${pruneResult.ok ? 'ok' : 'failed'}`);
  }
  if (!options.apply) {
    for (const item of planned) {
      console.log(`DRYRUN: git worktree remove "${item.path}"  # branch=${item.branch}`);
    }
  }
  console.log(`[worktree-cleanup] wrote ${outputPath}`);
};

const scriptPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
const modulePath = fileURLToPath(import.meta.url);
if (scriptPath === modulePath) {
  try {
    run();
  } catch (error) {
    console.error(`[worktree-cleanup] ${error instanceof Error ? error.message : String(error)}`);
    process.exit(1);
  }
}
