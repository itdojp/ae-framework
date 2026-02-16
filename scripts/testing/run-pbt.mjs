#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const EXIT_CODE_CONFIG_NOT_FOUND = 2;
const EXIT_CODE_RUNNER_NOT_FOUND = 127;

const DEFAULT_CONFIG_CANDIDATES = [
  'tests/property/vitest.config.ts',
  'tests/property/vitest.config.mts',
  'tests/property/vitest.config.js',
  'tests/property/vitest.config.mjs',
  'tests/property/vitest.config.cjs',
];

const DEFAULT_DIR_CANDIDATES = [
  'tests/property',
  'test/property',
];

export function parseArgs(argv) {
  const options = {
    explicitConfig: process.env.PBT_CONFIG?.trim() || null,
    passThrough: [],
    help: false,
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }

    if (arg === '--config' || arg === '-c') {
      if (next && !next.startsWith('-')) {
        options.explicitConfig = next;
        i += 1;
      }
      continue;
    }

    if (arg.startsWith('--config=')) {
      options.explicitConfig = arg.slice('--config='.length) || null;
      continue;
    }

    options.passThrough.push(arg);
  }

  return options;
}

export function resolvePbtPlan({
  cwd = process.cwd(),
  explicitConfig = null,
  existsSyncImpl = fs.existsSync,
  statSyncImpl = fs.statSync,
} = {}) {
  const searchedPaths = [];

  if (explicitConfig) {
    const explicitPath = path.resolve(cwd, explicitConfig);
    searchedPaths.push(explicitConfig);
    if (existsSyncImpl(explicitPath)) {
      return {
        mode: 'config',
        configPath: explicitPath,
        searchedPaths,
      };
    }
    return {
      mode: 'missing',
      reason: 'explicit-config-not-found',
      searchedPaths,
    };
  }

  for (const candidate of DEFAULT_CONFIG_CANDIDATES) {
    searchedPaths.push(candidate);
    const resolved = path.resolve(cwd, candidate);
    if (existsSyncImpl(resolved)) {
      return {
        mode: 'config',
        configPath: resolved,
        searchedPaths,
      };
    }
  }

  for (const candidate of DEFAULT_DIR_CANDIDATES) {
    searchedPaths.push(candidate);
    const resolved = path.resolve(cwd, candidate);
    try {
      if (existsSyncImpl(resolved) && statSyncImpl(resolved).isDirectory()) {
        return {
          mode: 'dir',
          testsDir: resolved,
          searchedPaths,
        };
      }
    } catch {
      // Ignore stat errors and continue to the next candidate.
    }
  }

  return {
    mode: 'missing',
    reason: 'no-config-or-tests-dir',
    searchedPaths,
  };
}

export function buildVitestCommand(plan, passThrough = [], cwd = process.cwd()) {
  const args = ['exec', 'vitest', 'run'];
  if (plan.mode === 'config') {
    const configArg = path.relative(cwd, plan.configPath) || plan.configPath;
    args.push('--config', configArg);
  } else if (plan.mode === 'dir') {
    const dirArg = path.relative(cwd, plan.testsDir) || plan.testsDir;
    args.push(dirArg);
  }
  args.push(...passThrough);
  return { command: 'pnpm', args };
}

function printHelp() {
  console.log(`Usage: pnpm run pbt [-- --config <path>] [vitest args...]

Resolves PBT execution in this order:
  1) tests/property/vitest.config.{ts,mts,js,mjs,cjs}
  2) tests/property directory fallback (vitest run tests/property)

Exit codes:
  0: success
  1: tests failed
  2: PBT config/tests directory not found
  127: runner (pnpm) not found
`);
}

export function runPbt(options, {
  cwd = process.cwd(),
  existsSyncImpl = fs.existsSync,
  spawnSyncImpl = spawnSync,
  logger = console,
} = {}) {
  if (options.help) {
    printHelp();
    return 0;
  }

  const plan = resolvePbtPlan({
    cwd,
    explicitConfig: options.explicitConfig,
    existsSyncImpl,
    statSyncImpl: fs.statSync,
  });

  if (plan.mode === 'missing') {
    const searched = plan.searchedPaths.map((entry) => `- ${entry}`).join('\n');
    logger.error('[pbt-runner] PBT_CONFIG_NOT_FOUND: property-test config or directory could not be resolved.');
    logger.error(`[pbt-runner] reason: ${plan.reason}`);
    logger.error('[pbt-runner] searched:');
    logger.error(searched);
    logger.error('[pbt-runner] hint: create tests/property/vitest.config.ts or tests/property/*.test.ts');
    return EXIT_CODE_CONFIG_NOT_FOUND;
  }

  const { command, args } = buildVitestCommand(plan, options.passThrough, cwd);
  const result = spawnSyncImpl(command, args, {
    cwd,
    env: process.env,
    stdio: 'inherit',
  });

  if (result.error) {
    if (result.error.code === 'ENOENT') {
      logger.error('[pbt-runner] pnpm not found in PATH');
      return EXIT_CODE_RUNNER_NOT_FOUND;
    }
    logger.error(`[pbt-runner] failed to start runner: ${String(result.error.message ?? result.error)}`);
    return 1;
  }

  return result.status ?? 1;
}

function isCliInvocation(argv) {
  if (!argv[1]) {
    return false;
  }
  try {
    return fileURLToPath(import.meta.url) === path.resolve(argv[1]);
  } catch {
    return false;
  }
}

if (isCliInvocation(process.argv)) {
  process.exit(runPbt(parseArgs(process.argv)));
}
