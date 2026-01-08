#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';

const PROFILE_COMMANDS = {
  all: [['pnpm', 'run', 'quality:run:all']],
  gates: [['pnpm', 'run', 'quality:gates']],
  policy: [['pnpm', 'run', 'quality:policy']],
};

export function listProfiles() {
  return Object.keys(PROFILE_COMMANDS);
}

export function resolveProfile(profile) {
  return PROFILE_COMMANDS[profile] ?? null;
}

function parseArgs(argv) {
  const options = {
    profile: null,
    list: false,
    dryRun: false,
    help: false,
    unknown: [],
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if ((arg === '--profile' || arg === '-p') && next) {
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
  console.log(`Usage: node scripts/quality/run.mjs --profile <name> [--list] [--dry-run]

Options:
  -p, --profile <name>   Profile name (e.g. all, gates, policy)
  --list                 Print available profiles
  --dry-run              Print resolved commands without executing
  -h, --help             Show this message
`);
}

function runQuality(options) {
  if (options.help) {
    printHelp();
    return 0;
  }

  if (options.list) {
    console.log(listProfiles().join('\n'));
    return 0;
  }

  if (options.unknown.length > 0) {
    console.error(`[quality-runner] unknown args: ${options.unknown.join(' ')}`);
    return 3;
  }

  if (!options.profile) {
    console.error('[quality-runner] missing --profile');
    return 3;
  }

  const commands = resolveProfile(options.profile);
  if (!commands) {
    console.error(`[quality-runner] unknown profile: ${options.profile}`);
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
    if (result.status !== 0) {
      return result.status ?? 1;
    }
  }
  return 0;
}

function isCliInvocation(argv) {
  return import.meta.url === pathToFileURL(argv[1]).href;
}

if (isCliInvocation(process.argv)) {
  process.exit(runQuality(parseArgs(process.argv)));
}
