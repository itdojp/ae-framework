#!/usr/bin/env node

import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const DEFAULT_NODE_RANGE = '>=20.11 <23';
const DEFAULT_PACKAGE_MANAGER = 'pnpm@10.0.0';
const DIST_CANDIDATES = [
  'dist/src/cli/index.js',
  'dist/cli.js',
];
const EXIT_CODES = {
  SUCCESS: 0,
  ERROR: 1,
  WARNING: 2,
  INVALID_ARGUMENT: 3,
};

function parseNodeVersion(versionText) {
  const match = /^v?(\d+)\.(\d+)\.(\d+)/.exec(versionText.trim());
  if (!match) {
    return null;
  }
  return {
    major: Number(match[1]),
    minor: Number(match[2]),
    patch: Number(match[3]),
    raw: `${match[1]}.${match[2]}.${match[3]}`,
  };
}

function parseNodeRange(rangeText) {
  const match = /^>=\s*(\d+)\.(\d+)\s*<\s*(\d+)/.exec(rangeText.trim());
  if (!match) {
    return {
      minMajor: 20,
      minMinor: 11,
      maxMajorExclusive: 23,
    };
  }
  return {
    minMajor: Number(match[1]),
    minMinor: Number(match[2]),
    maxMajorExclusive: Number(match[3]),
  };
}

function satisfiesNodeRange(version, range) {
  if (version.major < range.minMajor) {
    return false;
  }
  if (version.major === range.minMajor && version.minor < range.minMinor) {
    return false;
  }
  if (version.major >= range.maxMajorExclusive) {
    return false;
  }
  return true;
}

function runVersionCommand(command, deps) {
  const result = deps.spawn(command, ['--version'], {
    cwd: deps.rootDir,
    stdio: 'pipe',
    encoding: 'utf8',
  });
  if (result.error) {
    return null;
  }
  if ((result.status ?? 1) !== 0) {
    return null;
  }
  const output = `${result.stdout ?? ''}${result.stderr ?? ''}`.trim();
  if (!output) {
    return null;
  }
  const firstLine = output.split(/\r?\n/u)[0]?.trim() ?? output;
  return firstLine;
}

function loadProjectMetadata(rootDir) {
  try {
    const packageJson = JSON.parse(readFileSync(path.join(rootDir, 'package.json'), 'utf8'));
    return {
      nodeRange: packageJson.engines?.node || DEFAULT_NODE_RANGE,
      packageManager: packageJson.packageManager || DEFAULT_PACKAGE_MANAGER,
    };
  } catch {
    return {
      nodeRange: DEFAULT_NODE_RANGE,
      packageManager: DEFAULT_PACKAGE_MANAGER,
    };
  }
}

function extractExpectedPnpmVersion(packageManagerText) {
  const match = /^pnpm@(.+)$/.exec(packageManagerText.trim());
  return match ? match[1] : '10.0.0';
}

function parseArgs(argv = process.argv) {
  const options = {
    format: 'human',
    outputPath: path.join('artifacts', 'doctor', 'env.json'),
    rootDir: process.cwd(),
    help: false,
    unknown: [],
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg.startsWith('--format=')) {
      const value = arg.slice('--format='.length);
      if (value === 'human' || value === 'json' || value === 'both') {
        options.format = value;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    if (arg === '--format') {
      const next = argv[index + 1];
      if (next === 'human' || next === 'json' || next === 'both') {
        options.format = next;
        index += 1;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    if (arg.startsWith('--output=')) {
      const value = arg.slice('--output='.length);
      if (value) {
        options.outputPath = value;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    if (arg === '--output') {
      const next = argv[index + 1];
      if (next && !next.startsWith('-')) {
        options.outputPath = next;
        index += 1;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    if (arg.startsWith('--root=')) {
      const value = arg.slice('--root='.length);
      options.rootDir = path.resolve(value);
      continue;
    }
    if (arg === '--root') {
      const next = argv[index + 1];
      if (next && !next.startsWith('-')) {
        options.rootDir = path.resolve(next);
        index += 1;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    options.unknown.push(arg);
  }

  return options;
}

function pushCheck(checks, check) {
  checks.push({
    id: check.id,
    label: check.label,
    status: check.status,
    required: Boolean(check.required),
    value: check.value ?? '',
    message: check.message ?? '',
    action: check.action ?? '',
  });
}

function evaluateEnvironment(options, deps = {}) {
  const runtime = {
    processVersion: deps.processVersion ?? process.version,
    platform: deps.platform ?? process.platform,
    arch: deps.arch ?? process.arch,
    rootDir: options.rootDir,
  };
  const metadata = loadProjectMetadata(options.rootDir);
  const checks = [];

  const nodeVersion = parseNodeVersion(runtime.processVersion);
  const nodeRange = parseNodeRange(metadata.nodeRange);
  if (!nodeVersion) {
    pushCheck(checks, {
      id: 'node.version',
      label: 'Node.js version',
      status: 'error',
      required: true,
      value: runtime.processVersion,
      message: `Failed to parse Node.js version. Expected ${metadata.nodeRange}.`,
      action: `Install Node.js in range ${metadata.nodeRange}.`,
    });
  } else if (satisfiesNodeRange(nodeVersion, nodeRange)) {
    pushCheck(checks, {
      id: 'node.version',
      label: 'Node.js version',
      status: 'ok',
      required: true,
      value: `v${nodeVersion.raw}`,
      message: `Supported range: ${metadata.nodeRange}`,
    });
  } else {
    pushCheck(checks, {
      id: 'node.version',
      label: 'Node.js version',
      status: 'error',
      required: true,
      value: `v${nodeVersion.raw}`,
      message: `Outside supported range (${metadata.nodeRange}).`,
      action: `Use Node.js in range ${metadata.nodeRange}.`,
    });
  }

  const expectedPnpmVersion = extractExpectedPnpmVersion(metadata.packageManager);
  const pnpmVersionRaw = runVersionCommand('pnpm', {
    spawn: deps.spawn ?? spawnSync,
    rootDir: options.rootDir,
  });
  if (!pnpmVersionRaw) {
    pushCheck(checks, {
      id: 'pnpm.command',
      label: 'pnpm',
      status: 'error',
      required: true,
      value: 'not found',
      message: `Expected package manager: ${metadata.packageManager}`,
      action: `Run: corepack enable && corepack prepare ${metadata.packageManager} --activate`,
    });
  } else {
    const pnpmVersion = parseNodeVersion(pnpmVersionRaw);
    const expectedMajor = parseNodeVersion(expectedPnpmVersion)?.major;
    if (!pnpmVersion || (expectedMajor != null && pnpmVersion.major !== expectedMajor)) {
      pushCheck(checks, {
        id: 'pnpm.version',
        label: 'pnpm version',
        status: 'warn',
        required: false,
        value: pnpmVersionRaw,
        message: `Recommended: ${metadata.packageManager}`,
        action: `Run: corepack prepare ${metadata.packageManager} --activate`,
      });
    } else {
      pushCheck(checks, {
        id: 'pnpm.version',
        label: 'pnpm version',
        status: 'ok',
        required: true,
        value: pnpmVersionRaw,
      });
    }
  }

  const corepackVersionRaw = runVersionCommand('corepack', {
    spawn: deps.spawn ?? spawnSync,
    rootDir: options.rootDir,
  });
  if (!corepackVersionRaw) {
    pushCheck(checks, {
      id: 'corepack.command',
      label: 'corepack',
      status: 'warn',
      required: false,
      value: 'not found',
      message: 'corepack command was not found.',
      action: 'Install Node.js distribution with corepack enabled.',
    });
  } else {
    pushCheck(checks, {
      id: 'corepack.command',
      label: 'corepack',
      status: 'ok',
      required: false,
      value: corepackVersionRaw,
    });
  }

  const distCandidate = DIST_CANDIDATES.find((candidate) => existsSync(path.resolve(options.rootDir, candidate)));
  if (distCandidate) {
    pushCheck(checks, {
      id: 'dist.cli',
      label: 'dist CLI',
      status: 'ok',
      required: false,
      value: distCandidate,
    });
  } else {
    pushCheck(checks, {
      id: 'dist.cli',
      label: 'dist CLI',
      status: 'warn',
      required: false,
      value: DIST_CANDIDATES.join(', '),
      message: 'Built CLI was not found.',
      action: 'Run: pnpm run build',
    });
  }

  if (runtime.platform === 'win32') {
    pushCheck(checks, {
      id: 'os.platform',
      label: 'platform',
      status: 'ok',
      required: false,
      value: `${runtime.platform}/${runtime.arch}`,
      message: 'Windows detected.',
      action: 'Use WSL2 when path/tool compatibility issues occur.',
    });
  } else {
    pushCheck(checks, {
      id: 'os.platform',
      label: 'platform',
      status: 'ok',
      required: false,
      value: `${runtime.platform}/${runtime.arch}`,
    });
  }

  const counts = {
    ok: checks.filter((check) => check.status === 'ok').length,
    warn: checks.filter((check) => check.status === 'warn').length,
    error: checks.filter((check) => check.status === 'error').length,
  };

  const exitCode = counts.error > 0 ? EXIT_CODES.ERROR : (counts.warn > 0 ? EXIT_CODES.WARNING : EXIT_CODES.SUCCESS);
  return {
    schemaVersion: 'doctor-env/v1',
    generatedAt: (deps.nowIso ?? (() => new Date().toISOString()))(),
    rootDir: options.rootDir,
    outputPath: path.resolve(options.rootDir, options.outputPath),
    metadata: {
      packageManager: metadata.packageManager,
      nodeRange: metadata.nodeRange,
      platform: runtime.platform,
      arch: runtime.arch,
      nodeVersion: runtime.processVersion,
    },
    summary: {
      status: counts.error > 0 ? 'error' : (counts.warn > 0 ? 'warn' : 'ok'),
      counts,
      exitCode,
    },
    checks,
  };
}

function renderHumanReport(result) {
  const lines = [];
  lines.push('Environment diagnostics (doctor:env)');
  lines.push(`- status: ${result.summary.status}`);
  lines.push(`- ok/warn/error: ${result.summary.counts.ok}/${result.summary.counts.warn}/${result.summary.counts.error}`);
  lines.push(`- output: ${result.outputPath}`);
  lines.push('');
  lines.push('Checks:');
  for (const check of result.checks) {
    const icon = check.status === 'ok' ? 'OK' : (check.status === 'warn' ? 'WARN' : 'ERROR');
    lines.push(`- [${icon}] ${check.label}: ${check.value}`);
    if (check.message) {
      lines.push(`  - ${check.message}`);
    }
    if (check.action) {
      lines.push(`  - action: ${check.action}`);
    }
  }
  return `${lines.join('\n')}\n`;
}

function persistReport(result) {
  mkdirSync(path.dirname(result.outputPath), { recursive: true });
  writeFileSync(result.outputPath, JSON.stringify(result, null, 2));
}

export function runDoctorEnv(argv = process.argv, deps = {}) {
  const options = parseArgs(argv);
  if (options.help) {
    return {
      exitCode: EXIT_CODES.SUCCESS,
      options,
      result: null,
    };
  }
  if (options.unknown.length > 0) {
    return {
      exitCode: EXIT_CODES.INVALID_ARGUMENT,
      options,
      result: null,
    };
  }

  const result = evaluateEnvironment(options, deps);
  persistReport(result);

  if (options.format === 'human' || options.format === 'both') {
    process.stdout.write(renderHumanReport(result));
  }
  if (options.format === 'json' || options.format === 'both') {
    process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
  }

  return {
    exitCode: result.summary.exitCode,
    options,
    result,
  };
}

function printHelp() {
  process.stdout.write(`Usage: node scripts/doctor/doctor-env.mjs [options]

Options:
  --format <human|json|both>  Output format (default: human)
  --output <path>             JSON output path (default: artifacts/doctor/env.json)
  --root <dir>                Project root (default: current directory)
  -h, --help                  Show help
`);
}

export function main(argv = process.argv) {
  const outcome = runDoctorEnv(argv);
  if (outcome.options.help) {
    printHelp();
    return EXIT_CODES.SUCCESS;
  }
  if (outcome.options.unknown.length > 0) {
    process.stderr.write(`Unknown argument(s): ${outcome.options.unknown.join(', ')}\n`);
    printHelp();
    return EXIT_CODES.INVALID_ARGUMENT;
  }
  return outcome.exitCode;
}

export function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  if (!argvPath || typeof argvPath !== 'string') {
    return false;
  }
  try {
    return path.resolve(fileURLToPath(importMetaUrl)) === path.resolve(argvPath);
  } catch {
    return false;
  }
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  process.exitCode = main(process.argv);
}
