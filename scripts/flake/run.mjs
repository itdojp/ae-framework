#!/usr/bin/env node
/**
 * CLI entry point for running flake detection and isolation profiles.
 *
 * This script resolves a named "flake profile" (e.g. `detect`, `report`)
 * to one or more underlying package scripts and executes them sequentially.
 * It provides a consistent interface for flake workflows in CI and locally.
 *
 * Usage:
 *   node scripts/flake/run.mjs --profile <name> [--list] [--dry-run]
 *
 * Options:
 *   -p, --profile <name>   Name of the flake profile to run.
 *   --list                 Print all available profile names and exit.
 *   --dry-run              Print the resolved commands instead of executing them.
 *   -h, --help             Show this usage information and exit.
 *
 * Exit codes:
 *   0  - Success (including help or list output).
 *   2  - Unknown profile name.
 *   3  - Invalid or missing arguments.
 *   >0 - Non-zero exit code from a child flake command.
 */
import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const PROFILE_COMMANDS = {
  detect: [['pnpm', 'run', 'flake:detect']],
  'detect-quick': [['pnpm', 'run', 'flake:detect:quick']],
  'detect-thorough': [['pnpm', 'run', 'flake:detect:thorough']],
  'detect-enhanced': [['pnpm', 'run', 'flake:detect:enhanced']],
  'detect-enhanced-quick': [['pnpm', 'run', 'flake:detect:enhanced:quick']],
  'detect-enhanced-deep': [['pnpm', 'run', 'flake:detect:enhanced:deep']],
  isolate: [['pnpm', 'run', 'flake:isolate']],
  recover: [['pnpm', 'run', 'flake:recover']],
  report: [['pnpm', 'run', 'flake:report']],
  maintenance: [['pnpm', 'run', 'flake:maintenance']],
  remove: [['pnpm', 'run', 'flake:remove']],
  list: [['pnpm', 'run', 'flake:list']],
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
    if (arg === '--profile' || arg === '-p') {
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
  console.log(`Usage: node scripts/flake/run.mjs --profile <name> [--list] [--dry-run]

Options:
  -p, --profile <name>   Profile name (e.g. detect, report, isolate)
  --list                 Print available profiles
  --dry-run              Print resolved commands without executing
  -h, --help             Show this message
`);
}

export function runFlake(options) {
  if (options.help) {
    printHelp();
    return 0;
  }

  if (options.list) {
    console.log(listProfiles().join('\n'));
    return 0;
  }

  if (options.profileError) {
    console.error('[flake-runner] missing value for --profile');
    return 3;
  }

  if (options.unknown.length > 0) {
    console.error(`[flake-runner] unknown args: ${options.unknown.join(' ')}`);
    return 3;
  }

  if (!options.profile) {
    console.error('[flake-runner] missing --profile');
    return 3;
  }

  const commands = resolveProfile(options.profile);
  if (!commands) {
    console.error(`[flake-runner] unknown profile: ${options.profile}`);
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
        `[flake-runner] failed to spawn command: ${command.join(' ')}: ${result.error.message ?? result.error}`
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
  process.exit(runFlake(parseArgs(process.argv)));
}
