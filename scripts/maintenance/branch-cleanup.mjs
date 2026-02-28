#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

const DEFAULT_BASE_REF = 'origin/main';
const DEFAULT_REMOTE = 'origin';
const DEFAULT_SCOPE = 'local';
const DEFAULT_MAX = 200;
const DEFAULT_OUTPUT_JSON = 'tmp/maintenance/branch-cleanup-report.json';

const PROTECTED_EXACT = new Set(['main', 'master', 'develop', 'staging']);
const PROTECTED_PREFIXES = ['release/', 'hotfix/'];

const usage = () => {
  console.log(`Usage: node scripts/maintenance/branch-cleanup.mjs [options]

Options:
  --base <ref>          Base ref to compare merge status (default: ${DEFAULT_BASE_REF})
  --remote <name>       Remote name (default: ${DEFAULT_REMOTE})
  --scope <mode>        local | remote | both (default: ${DEFAULT_SCOPE})
  --max <n>             Max branches to process per scope (default: ${DEFAULT_MAX})
  --output-json <path>  JSON output path (default: ${DEFAULT_OUTPUT_JSON})
  --apply               Execute deletion (without this, dry-run only)
  --help                Show this help
`);
};

const parseArgs = (argv) => {
  const options = {
    base: DEFAULT_BASE_REF,
    remote: DEFAULT_REMOTE,
    scope: DEFAULT_SCOPE,
    max: DEFAULT_MAX,
    outputJson: DEFAULT_OUTPUT_JSON,
    apply: false,
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
    if (arg === '--scope') {
      options.scope = String(argv[++i] || '').trim();
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

try {
  const options = parseArgs(process.argv.slice(2));
  const generatedAt = new Date().toISOString();
  const currentBranch = runGit(['branch', '--show-current']);
  const shouldLocal = options.scope === 'local' || options.scope === 'both';
  const shouldRemote = options.scope === 'remote' || options.scope === 'both';

  const mergedLocal = new Set(
    parseBranchList(runGit(['branch', '--format=%(refname:short)', '--merged', options.base])),
  );
  const mergedRemote = new Set(
    parseBranchList(runGit(['branch', '-r', '--format=%(refname:short)', '--merged', options.base])),
  );

  const localCandidates = shouldLocal
    ? parseBranchList(runGit(['branch', '--format=%(refname:short)']))
        .filter((name) => mergedLocal.has(name))
        .filter((name) => name !== currentBranch)
        .filter((name) => !isProtected(name))
        .sort()
    : [];

  const remoteCandidates = shouldRemote
    ? parseBranchList(runGit(['branch', '-r', '--format=%(refname:short)']))
        .filter((name) => name.startsWith(`${options.remote}/`))
        .filter((name) => name !== `${options.remote}/HEAD`)
        .filter((name) => mergedRemote.has(name))
        .map((name) => name.slice(options.remote.length + 1))
        .filter((name) => !isProtected(name))
        .sort()
    : [];

  const localResult = {
    totalCandidates: localCandidates.length,
    planned: localCandidates.slice(0, options.max),
    considered: [],
    deleted: [],
    failed: [],
  };
  const remoteResult = {
    totalCandidates: remoteCandidates.length,
    planned: remoteCandidates.slice(0, options.max),
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
    for (const branch of remoteCandidates) {
      if (remoteResult.deleted.length >= options.max) break;
      remoteResult.considered.push(branch);
      const result = runGitSafe(['push', options.remote, '--delete', branch]);
      if (result.ok) {
        remoteResult.deleted.push(branch);
      } else {
        remoteResult.failed.push({ branch, reason: result.message || result.output });
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
  console.log(
    `[branch-cleanup] local candidates=${localCandidates.length}, remote candidates=${remoteCandidates.length}`,
  );
  if (!options.apply) {
    if (shouldLocal) {
      for (const branch of localResult.planned) {
        console.log(`DRYRUN local: git branch -d ${branch}`);
      }
    }
    if (shouldRemote) {
      for (const branch of remoteResult.planned) {
        console.log(`DRYRUN remote: git push ${options.remote} --delete ${branch}`);
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
} catch (error) {
  console.error(`[branch-cleanup] ${error instanceof Error ? error.message : String(error)}`);
  process.exit(1);
}
