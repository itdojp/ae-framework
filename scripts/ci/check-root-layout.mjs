#!/usr/bin/env node

import { readdirSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const ALLOWED_ROOT_ENTRIES = new Set([
  '.ae',
  '.devcontainer',
  '.dependency-cruiser.js',
  '.dockerignore',
  '.editorconfig',
  '.env.example',
  '.gitattributes',
  '.github',
  '.gitignore',
  '.gitleaks.toml',
  '.npmrc',
  '.nycrc.json',
  '.tool-versions',
  'AGENTS.md',
  'CONTRIBUTING.md',
  'LICENSE',
  'README.md',
  'SECURITY.md',
  '_apalache-out',
  'api',
  'apps',
  'artifacts',
  'benchmarks',
  'codex',
  'config',
  'configs',
  'contracts',
  'docker',
  'docs',
  'eslint.config.js',
  'examples',
  'fixtures',
  'infra',
  'metrics',
  'observability',
  'package.json',
  'packages',
  'plans',
  'pnpm-lock.yaml',
  'pnpm-workspace.yaml',
  'podman',
  'policies',
  'policy',
  'presets',
  'proofs',
  'reports',
  'samples',
  'schema',
  'scripts',
  'security',
  'spec',
  'src',
  'templates',
  'test-cassettes',
  'temp-reports',
  'tests',
  'tsconfig.json',
  'types',
  'vitest.config.ts',
]);

export const FORBIDDEN_ROOT_PATTERNS = [
  { pattern: /^cegis-report-\d+\.json$/, reason: 'ephemeral CEGIS report in repository root' },
  { pattern: /^drift-report-[\w.-]+\.json$/, reason: 'ephemeral codegen drift report in repository root' },
  { pattern: /^generated-[\w.-]+\.json$/, reason: 'ephemeral integration generated file in repository root' },
  { pattern: /^filtered-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^parallel-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^run-suite\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^run-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^workflow-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^conformance-results\.json$/, reason: 'conformance output must not be emitted to repository root' },
  { pattern: /^verify-lite-run-summary\.json$/, reason: 'verify-lite run summary must be under artifacts/verify-lite/' },
  { pattern: /^verify-lite-lint-summary\.json$/, reason: 'verify-lite lint summary must be under artifacts/verify-lite/ or reports/lint/' },
  { pattern: /^verify-lite-lint\.log$/, reason: 'verify-lite lint log must be under artifacts/verify-lite/' },
  { pattern: /^node_modules$/, reason: 'dependency cache directory in repository root' },
  { pattern: /^coverage$/, reason: 'coverage output directory in repository root' },
  { pattern: /^test-results$/, reason: 'test result directory in repository root' },
  { pattern: /^test-results-run$/, reason: 'test result directory in repository root' },
  { pattern: /^tmp$/, reason: 'temporary directory in repository root' },
];

/**
 * Classify repository root entries into blocking violations and non-blocking warnings.
 *
 * @param {string[]} entries - Root entry names.
 * @returns {{violations: Array<{entry: string, reason: string, type: string}>, warnings: Array<{entry: string, reason: string, type: string}>}}
 */
export function scanRootLayout(entries) {
  const violations = [];
  const warnings = [];
  const sorted = [...entries].sort((a, b) => a.localeCompare(b));

  for (const entry of sorted) {
    const forbidden = FORBIDDEN_ROOT_PATTERNS.find(({ pattern }) => pattern.test(entry));
    if (forbidden) {
      violations.push({ entry, reason: forbidden.reason, type: 'forbidden_pattern' });
      continue;
    }

    if (entry.startsWith('.')) {
      continue;
    }

    if (!ALLOWED_ROOT_ENTRIES.has(entry)) {
      warnings.push({ entry, reason: 'not in allowed root entry list', type: 'unclassified_entry' });
    }
  }

  return { violations, warnings };
}

function parseArgs(argv) {
  let format = 'text';
  let mode = 'strict';
  let rootDir = process.cwd();

  for (const arg of argv.slice(2)) {
    if (arg.startsWith('--format=')) {
      const value = arg.slice('--format='.length);
      if (value === 'json' || value === 'text') format = value;
      continue;
    }
    if (arg.startsWith('--mode=')) {
      const value = arg.slice('--mode='.length);
      if (value === 'strict' || value === 'warn') mode = value;
      continue;
    }
    if (arg.startsWith('--root=')) {
      rootDir = path.resolve(arg.slice('--root='.length));
    }
  }

  return { format, mode, rootDir };
}

function renderText(result, options) {
  const lines = [];
  lines.push('Root layout check');
  lines.push(`- mode: ${options.mode}`);
  lines.push(`- root: ${options.rootDir}`);
  lines.push(`- violations: ${result.violations.length}`);
  lines.push(`- warnings: ${result.warnings.length}`);

  if (result.violations.length > 0) {
    lines.push('');
    lines.push('Violations:');
    for (const item of result.violations) {
      lines.push(`- ${item.entry}: ${item.reason}`);
    }
  }

  if (result.warnings.length > 0) {
    lines.push('');
    lines.push('Warnings:');
    for (const item of result.warnings) {
      lines.push(`- ${item.entry}: ${item.reason}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

/**
 * Emit check result in configured output format.
 *
 * @param {{violations: Array<{entry: string, reason: string, type: string}>, warnings: Array<{entry: string, reason: string, type: string}>}} result - Scan result.
 * @param {{mode: string, format: string, rootDir: string}} options - Parsed command options.
 * @param {number} exitCode - Exit code derived from mode and result.
 */
function writeResult(result, options, exitCode) {
  if (options.format === 'json') {
    process.stdout.write(JSON.stringify({
      root: options.rootDir,
      mode: options.mode,
      violations: result.violations,
      warnings: result.warnings,
      exitCode,
    }, null, 2));
    process.stdout.write('\n');
    return;
  }
  process.stdout.write(renderText(result, options));
}

/**
 * Run root layout validation and print the result.
 *
 * @param {string[]} [argv=process.argv] - Process arguments.
 * @returns {{violations: Array<{entry: string, reason: string, type: string}>, warnings: Array<{entry: string, reason: string, type: string}>, exitCode: number, options: {format: string, mode: string, rootDir: string}}}
 */
export function runRootLayoutCheck(argv = process.argv) {
  const options = parseArgs(argv);
  let entries;
  try {
    entries = readdirSync(options.rootDir, { encoding: 'utf8' })
      .filter((name) => name !== '.git');
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    const failure = {
      violations: [{
        entry: options.rootDir,
        reason: `failed to read root directory: ${message}`,
        type: 'read_error',
      }],
      warnings: [],
    };
    const exitCode = 1;
    writeResult(failure, options, exitCode);
    return { ...failure, exitCode, options };
  }

  const result = scanRootLayout(entries);
  const hasError = result.violations.length > 0;
  const exitCode = options.mode === 'warn' ? 0 : (hasError ? 1 : 0);
  writeResult(result, options, exitCode);

  return { ...result, exitCode, options };
}

export function isExecutedAsMain(metaUrl, argvPath = process.argv[1]) {
  if (!argvPath || typeof argvPath !== 'string') {
    return false;
  }
  try {
    const modulePath = path.resolve(fileURLToPath(metaUrl));
    const entryPath = path.resolve(argvPath);
    return modulePath === entryPath;
  } catch {
    return false;
  }
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  const outcome = runRootLayoutCheck(process.argv);
  process.exit(outcome.exitCode);
}
