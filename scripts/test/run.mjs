#!/usr/bin/env node
/**
 * CLI entry point for running test profiles.
 *
 * This script resolves a named "test profile" (e.g. `ci-lite`, `fast`)
 * to one or more underlying package scripts and executes them sequentially.
 * It provides a consistent interface for test workflows in CI and locally.
 *
 * Usage:
 *   node scripts/test/run.mjs --profile <name> [--list] [--dry-run]
 *
 * Options:
 *   -p, --profile <name>   Name of the test profile to run.
 *   --list                 Print all available profile names and exit.
 *   --dry-run              Print the resolved commands instead of executing them.
 *   -h, --help             Show this usage information and exit.
 *
 * Exit codes:
 *   0  - Success (including help or list output).
 *   2  - Unknown profile name.
 *   3  - Invalid or missing arguments.
 *   >0 - Non-zero exit code from a child test command.
 */
import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const PROFILE_COMMANDS = {
  all: [['pnpm', 'run', 'test:all']],
  fast: [['pnpm', 'run', 'test:fast']],
  'fast-plus': [['pnpm', 'run', 'test:fast:plus']],
  unit: [['pnpm', 'run', 'test:unit']],
  integration: [['pnpm', 'run', 'test:int']],
  perf: [['pnpm', 'run', 'test:perf']],
  ci: [['pnpm', 'run', 'test:ci']],
  'ci-stable': [['pnpm', 'run', 'test:ci:stable']],
  'ci-lite': [['pnpm', 'run', 'test:ci:lite']],
  'ci-extended': [['pnpm', 'run', 'test:ci:extended']],
};

export function listProfiles() {
  return Object.keys(PROFILE_COMMANDS);
}

export function resolveProfile(profile) {
  return Object.prototype.hasOwnProperty.call(PROFILE_COMMANDS, profile)
    ? PROFILE_COMMANDS[profile]
    : null;
}

export function parseArgs(argv) {
  const options = {
    profile: null,
    list: false,
    dryRun: false,
    help: false,
    profileError: false,
    unknown: [],
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if (arg.startsWith('--profile=')) {
      const value = arg.slice('--profile='.length);
      if (!value) {
        options.profileError = true;
        continue;
      }
      options.profile = value;
    } else if (arg.startsWith('-p=')) {
      const value = arg.slice('-p='.length);
      if (!value) {
        options.profileError = true;
        continue;
      }
      options.profile = value;
    } else if (arg === '--profile' || arg === '-p') {
      if (!next || next.startsWith('-')) {
        options.profileError = true;
        continue;
      }
      options.profile = next;
      i += 1;
    } else if (arg === '--list') {
      options.list = true;
    } else if (arg === '--dry-run') {
      options.dryRun = true;
    } else if (arg === '--help' || arg === '-h') {
      options.help = true;
    } else {
      options.unknown.push(arg);
    }
  }

  return options;
}

function printHelp() {
  console.log(`Usage: node scripts/test/run.mjs --profile <name> [--list] [--dry-run]

Options:
  -p, --profile <name>   Profile name (e.g. ci-lite, fast, unit)
  --list                 Print available profiles
  --dry-run              Print resolved commands without executing
  -h, --help             Show this message
`);
}

export function runTest(options) {
  if (options.help) {
    printHelp();
    return 0;
  }

  if (options.list) {
    console.log(listProfiles().join('\n'));
    return 0;
  }

  if (options.profileError) {
    console.error('[test-runner] missing value for --profile');
    return 3;
  }

  if (options.unknown.length > 0) {
    console.error(`[test-runner] unknown args: ${options.unknown.join(' ')}`);
    return 3;
  }

  if (!options.profile) {
    console.error('[test-runner] missing --profile');
    return 3;
  }

  const commands = resolveProfile(options.profile);
  if (!commands) {
    console.error(`[test-runner] unknown profile: ${options.profile}`);
    return 2;
  }

  if (options.dryRun) {
    for (const command of commands) {
      console.log(command.join(' '));
    }
    return 0;
  }

  for (const command of commands) {
    const result = spawnSync(command[0], command.slice(1), {
      stdio: 'inherit',
      env: process.env,
    });
    if (result.error) {
      console.error(
        `[test-runner] failed to spawn command: ${command.join(' ')}: ${result.error.message ?? result.error}`
      );
      return result.error.code === 'ENOENT' ? 127 : 1;
    }
    if (result.status !== 0) {
      return result.status ?? 1;
    }
  }
  return 0;
}

export function isCliInvocation(argv) {
  if (!argv[1]) return false;
  try {
    return fileURLToPath(import.meta.url) === path.resolve(argv[1]);
  } catch {
    return false;
  }
}

if (isCliInvocation(process.argv)) {
  process.exit(runTest(parseArgs(process.argv)));
}
