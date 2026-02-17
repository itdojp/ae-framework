#!/usr/bin/env node

import { readdirSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const FORBIDDEN_ROOT_GENERATED_PATTERNS = [
  { pattern: /^cegis-report-\d+\.json$/, reason: 'ephemeral CEGIS report in repository root' },
  { pattern: /^drift-report-[\w.-]+\.json$/, reason: 'ephemeral codegen drift report in repository root' },
  { pattern: /^generated-[\w.-]+\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^filtered-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^parallel-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^run-suite\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^run-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^workflow-test\.json$/, reason: 'ephemeral integration output in repository root' },
  { pattern: /^conformance-results\.json$/, reason: 'conformance output must not be emitted to repository root' },
  { pattern: /^verify-lite-run-summary\.json$/, reason: 'verify-lite run summary must be under artifacts/verify-lite/' },
  { pattern: /^verify-lite-lint-summary\.json$/, reason: 'verify-lite lint summary must be under artifacts/verify-lite/ or reports/lint/' },
  { pattern: /^verify-lite-lint\.log$/, reason: 'verify-lite lint log must be under artifacts/verify-lite/' },
];

function parseArgs(argv) {
  let rootDir = process.cwd();
  let format = 'text';
  for (const arg of argv.slice(2)) {
    if (arg.startsWith('--root=')) {
      rootDir = path.resolve(arg.slice('--root='.length));
      continue;
    }
    if (arg.startsWith('--format=')) {
      const value = arg.slice('--format='.length);
      if (value === 'text' || value === 'json') {
        format = value;
      }
    }
  }
  return { rootDir, format };
}

export function scanRootGeneratedFiles(entries) {
  const violations = [];
  for (const entry of [...entries].sort((a, b) => a.localeCompare(b))) {
    const matched = FORBIDDEN_ROOT_GENERATED_PATTERNS.find(({ pattern }) => pattern.test(entry));
    if (!matched) {
      continue;
    }
    violations.push({
      entry,
      reason: matched.reason,
      type: 'forbidden_generated_file',
    });
  }
  return violations;
}

function renderText(rootDir, violations) {
  const lines = [];
  lines.push('Root generated-file check');
  lines.push(`- root: ${rootDir}`);
  lines.push(`- violations: ${violations.length}`);
  if (violations.length > 0) {
    lines.push('');
    lines.push('Violations:');
    for (const violation of violations) {
      lines.push(`- ${violation.entry}: ${violation.reason}`);
    }
  }
  return `${lines.join('\n')}\n`;
}

export function runRootGeneratedFilesCheck(argv = process.argv) {
  const options = parseArgs(argv);
  let entries;
  try {
    entries = readdirSync(options.rootDir, { encoding: 'utf8' })
      .filter((name) => name !== '.git');
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    const failures = [{
      entry: options.rootDir,
      reason: `failed to read root directory: ${message}`,
      type: 'read_error',
    }];
    const exitCode = 1;
    if (options.format === 'json') {
      process.stdout.write(JSON.stringify({ root: options.rootDir, violations: failures, exitCode }, null, 2));
      process.stdout.write('\n');
    } else {
      process.stdout.write(renderText(options.rootDir, failures));
    }
    return { root: options.rootDir, violations: failures, exitCode };
  }

  const violations = scanRootGeneratedFiles(entries);
  const exitCode = violations.length > 0 ? 1 : 0;
  if (options.format === 'json') {
    process.stdout.write(JSON.stringify({ root: options.rootDir, violations, exitCode }, null, 2));
    process.stdout.write('\n');
  } else {
    process.stdout.write(renderText(options.rootDir, violations));
  }
  return { root: options.rootDir, violations, exitCode };
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
  const result = runRootGeneratedFilesCheck(process.argv);
  process.exit(result.exitCode);
}
