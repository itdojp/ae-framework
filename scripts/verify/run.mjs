#!/usr/bin/env node
/**
 * CLI entry point for running verification profiles.
 *
 * This script resolves a named "verify profile" (e.g. `fast`, `full`, `lite`)
 * to one or more underlying package scripts and executes them in order.
 * It can emit a machine-readable summary for CI.
 *
 * Usage:
 *   node scripts/verify/run.mjs --profile <name> [--list] [--dry-run] [--json] [--out <file>]
 */
import { spawnSync } from 'node:child_process';
import { mkdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const PROFILE_STEPS = {
  lite: [
    {
      name: 'verify:lite',
      command: ['bash', 'scripts/ci/run-verify-lite-local.sh'],
      required: true,
    },
  ],
  conformance: [
    {
      name: 'verify:conformance',
      command: ['node', 'scripts/formal/verify-conformance.mjs'],
      required: true,
    },
  ],
  formal: [
    {
      name: 'verify:formal',
      command: ['pnpm', 'run', 'verify:formal'],
      required: true,
    },
  ],
  fast: [
    {
      name: 'build',
      command: ['pnpm', 'run', 'build'],
      required: true,
    },
    {
      name: 'codex:quickstart',
      command: ['pnpm', 'run', 'codex:quickstart'],
      required: false,
    },
    {
      name: 'verify:lite',
      command: ['bash', 'scripts/ci/run-verify-lite-local.sh'],
      required: true,
    },
    {
      name: 'mbt',
      command: ['pnpm', 'run', 'mbt'],
      required: false,
    },
  ],
  full: [
    {
      name: 'build',
      command: ['pnpm', 'run', 'build'],
      required: true,
    },
    {
      name: 'codex:quickstart',
      command: ['pnpm', 'run', 'codex:quickstart'],
      required: false,
    },
    {
      name: 'verify:lite',
      command: ['bash', 'scripts/ci/run-verify-lite-local.sh'],
      required: true,
    },
    {
      name: 'mbt',
      command: ['pnpm', 'run', 'mbt'],
      required: false,
    },
    {
      name: 'pbt',
      command: ['pnpm', 'run', 'pbt'],
      required: false,
    },
    {
      name: 'mutation',
      command: ['pnpm', 'run', 'mutation'],
      required: false,
    },
    {
      name: 'verify:formal',
      command: ['pnpm', 'run', 'verify:formal'],
      required: false,
    },
  ],
};

const SUMMARY_SCHEMA_VERSION = 'verify-profile-summary/v1';

export function listProfiles() {
  return Object.keys(PROFILE_STEPS);
}

export function resolveProfileSteps(profile) {
  return Object.prototype.hasOwnProperty.call(PROFILE_STEPS, profile)
    ? PROFILE_STEPS[profile]
    : null;
}

export function resolveProfile(profile) {
  const steps = resolveProfileSteps(profile);
  return steps ? steps.map((step) => step.command) : null;
}

export function parseArgs(argv) {
  const options = {
    profile: null,
    list: false,
    dryRun: false,
    help: false,
    json: false,
    out: null,
    profileError: false,
    outError: false,
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
    } else if (arg.startsWith('--out=')) {
      const value = arg.slice('--out='.length);
      if (!value) {
        options.outError = true;
        continue;
      }
      options.out = value;
    } else if (arg === '--out') {
      if (!next || next.startsWith('-')) {
        options.outError = true;
        continue;
      }
      options.out = next;
      i += 1;
    } else if (arg === '--list') {
      options.list = true;
    } else if (arg === '--dry-run') {
      options.dryRun = true;
    } else if (arg === '--json') {
      options.json = true;
    } else if (arg === '--help' || arg === '-h') {
      options.help = true;
    } else {
      options.unknown.push(arg);
    }
  }

  return options;
}

function printHelp() {
  console.log(`Usage: node scripts/verify/run.mjs --profile <name> [--list] [--dry-run] [--json] [--out <file>]

Options:
  -p, --profile <name>   Profile name (${listProfiles().join(', ')})
  --list                 Print available profiles
  --dry-run              Print resolved commands without executing
  --json                 Emit JSON summary to stdout
  --out <file>           Write JSON summary to file
  -h, --help             Show this message
`);
}

function nowIso() {
  return new Date().toISOString();
}

function writeSummaryFile(outPath, summary) {
  const absolute = path.resolve(outPath);
  mkdirSync(path.dirname(absolute), { recursive: true });
  writeFileSync(absolute, JSON.stringify(summary, null, 2));
  return absolute;
}

function createStepSummary(step, extra = {}) {
  return {
    name: step.name,
    required: step.required,
    command: step.command.join(' '),
    ...extra,
  };
}

function runStep(step, extraArgs, captureOutput) {
  const startedAt = Date.now();
  const result = spawnSync(step.command[0], [...step.command.slice(1), ...extraArgs], {
    stdio: captureOutput ? ['ignore', 'pipe', 'pipe'] : 'inherit',
    env: process.env,
  });
  const durationMs = Date.now() - startedAt;

  if (result.error) {
    const code = result.error.code === 'ENOENT' ? 127 : 1;
    return {
      status: 'failed',
      exit_code: code,
      duration_ms: durationMs,
      error: String(result.error.message ?? result.error),
    };
  }

  const exitCode = result.status ?? 1;
  const status = exitCode === 0 ? 'passed' : 'failed';
  const summary = {
    status,
    exit_code: exitCode,
    duration_ms: durationMs,
  };
  if (captureOutput) {
    return {
      ...summary,
      stdout: result.stdout?.toString('utf8') ?? '',
      stderr: result.stderr?.toString('utf8') ?? '',
    };
  }
  return summary;
}

function emitSummary(summary, options) {
  if (options.out) {
    const savedPath = writeSummaryFile(options.out, summary);
    if (!options.json) {
      console.log(`[verify-runner] summary written: ${savedPath}`);
    }
  }
  if (options.json) {
    console.log(JSON.stringify(summary, null, 2));
  }
}

export function runVerify(options) {
  if (options.help) {
    printHelp();
    return 0;
  }

  if (options.list) {
    console.log(listProfiles().join('\n'));
    return 0;
  }

  if (options.profileError) {
    console.error('[verify-runner] missing value for --profile');
    return 3;
  }

  if (options.outError) {
    console.error('[verify-runner] missing value for --out');
    return 3;
  }

  if (!options.profile) {
    console.error('[verify-runner] missing --profile');
    return 3;
  }

  const steps = resolveProfileSteps(options.profile);
  if (!steps) {
    console.error(`[verify-runner] unknown profile: ${options.profile}`);
    return 2;
  }

  const startedAt = nowIso();
  const stepResults = [];
  let blockedByRequiredFailure = false;
  let firstRequiredFailureExitCode = 1;
  const extraArgs = options.unknown;
  const captureOutput = options.json;

  for (const step of steps) {
    if (options.dryRun) {
      if (!options.json) {
        console.log([...step.command, ...extraArgs].join(' '));
      }
      stepResults.push(
        createStepSummary(step, {
          status: 'skipped',
          exit_code: null,
          duration_ms: 0,
          reason: 'dry_run',
        })
      );
      continue;
    }

    if (blockedByRequiredFailure) {
      stepResults.push(
        createStepSummary(step, {
          status: 'skipped',
          exit_code: null,
          duration_ms: 0,
          reason: 'blocked_by_required_failure',
        })
      );
      continue;
    }

    const stepResult = runStep(step, extraArgs, captureOutput);
    stepResults.push(createStepSummary(step, stepResult));

    if (stepResult.status === 'failed' && step.required) {
      blockedByRequiredFailure = true;
      firstRequiredFailureExitCode = stepResult.exit_code || 1;
    }
  }

  const requiredFailCount = stepResults.filter((step) => step.required && step.status === 'failed').length;
  const optionalFailCount = stepResults.filter((step) => !step.required && step.status === 'failed').length;
  const finishedAt = nowIso();
  const overallStatus = requiredFailCount === 0 ? 'pass' : 'fail';

  const summary = {
    schemaVersion: SUMMARY_SCHEMA_VERSION,
    profile: options.profile,
    started_at: startedAt,
    finished_at: finishedAt,
    overall_status: overallStatus,
    required_fail_count: requiredFailCount,
    optional_fail_count: optionalFailCount,
    steps: stepResults,
  };

  emitSummary(summary, options);

  if (options.dryRun) {
    return 0;
  }

  return requiredFailCount > 0 ? firstRequiredFailureExitCode : 0;
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
  process.exit(runVerify(parseArgs(process.argv)));
}
