#!/usr/bin/env node

import { readdirSync } from 'node:fs';
import path from 'node:path';

export const ALLOWED_ROOT_ENTRIES = new Set([
  '.ae',
  '.devcontainer',
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
  'samples',
  'schema',
  'scripts',
  'security',
  'spec',
  'src',
  'templates',
  'test-cassettes',
  'tests',
  'tsconfig.json',
  'types',
  'vitest.config.ts',
]);

export const FORBIDDEN_ROOT_PATTERNS = [
  { pattern: /^cegis-report-\d+\.json$/, reason: 'ephemeral CEGIS report in repository root' },
  { pattern: /^generated-[\w.-]+\.json$/, reason: 'ephemeral integration generated file in repository root' },
  { pattern: /^filtered-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^parallel-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^run-suite\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^run-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^workflow-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^conformance-results\.json$/, reason: 'conformance output must not be emitted to repository root' },
  { pattern: /^verify-lite-lint-summary\.json$/, reason: 'verify-lite lint summary must be under reports/lint/' },
  { pattern: /^node_modules$/, reason: 'dependency cache directory in repository root' },
  { pattern: /^coverage$/, reason: 'coverage output directory in repository root' },
  { pattern: /^test-results$/, reason: 'test result directory in repository root' },
  { pattern: /^test-results-run$/, reason: 'test result directory in repository root' },
  { pattern: /^tmp$/, reason: 'temporary directory in repository root' },
];

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

export function runRootLayoutCheck(argv = process.argv) {
  const options = parseArgs(argv);
  const entries = readdirSync(options.rootDir, { encoding: 'utf8' })
    .filter((name) => name !== '.git');
  const result = scanRootLayout(entries);
  const hasError = result.violations.length > 0;
  const exitCode = options.mode === 'warn' ? 0 : (hasError ? 1 : 0);

  if (options.format === 'json') {
    process.stdout.write(JSON.stringify({
      root: options.rootDir,
      mode: options.mode,
      violations: result.violations,
      warnings: result.warnings,
      exitCode,
    }, null, 2));
    process.stdout.write('\n');
  } else {
    process.stdout.write(renderText(result, options));
  }

  return { ...result, exitCode, options };
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const outcome = runRootLayoutCheck(process.argv);
  process.exit(outcome.exitCode);
}
