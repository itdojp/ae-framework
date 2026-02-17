#!/usr/bin/env node

import { existsSync, lstatSync, rmSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { globSync } from 'glob';

export const SAFE_REMOVE_FILE_PATTERNS = [
  'cegis-report-*.json',
  'generated-*.json',
  'filtered-test.json',
  'parallel-test.json',
  'run-suite.json',
  'run-test.json',
  'workflow-test.json',
  'conformance-results.json',
  'verify-lite-lint-summary.json',
];

export const SAFE_REMOVE_DIRS = [
  'coverage',
  'test-results',
  'test-results-run',
  'tmp',
];

export const OPTIONAL_SAFE_REMOVE_DIRS = [
  'node_modules',
];

function sortUnique(values) {
  return [...new Set(values)].sort((a, b) => a.localeCompare(b));
}

export function collectSafeRemoveTargets(
  rootDir = process.cwd(),
  { includeNodeModules = false } = {},
) {
  const files = [];
  for (const pattern of SAFE_REMOVE_FILE_PATTERNS) {
    const matched = globSync(pattern, { cwd: rootDir, nodir: true, dot: false });
    files.push(...matched);
  }

  const dirs = [];
  const dirCandidates = includeNodeModules
    ? [...SAFE_REMOVE_DIRS, ...OPTIONAL_SAFE_REMOVE_DIRS]
    : SAFE_REMOVE_DIRS;
  for (const dirName of dirCandidates) {
    const target = path.join(rootDir, dirName);
    if (!existsSync(target)) {
      continue;
    }
    try {
      if (lstatSync(target).isDirectory()) {
        dirs.push(dirName);
      }
    } catch {
      // Skip targets that cannot be stat'ed.
    }
  }

  return {
    files: sortUnique(files),
    dirs: sortUnique(dirs),
  };
}

export function cleanRootSafeRemove(
  rootDir = process.cwd(),
  { dryRun = false, includeNodeModules = false } = {},
) {
  const targets = collectSafeRemoveTargets(rootDir, { includeNodeModules });
  const removed = [];
  const failed = [];

  for (const relPath of [...targets.files, ...targets.dirs]) {
    const absPath = path.join(rootDir, relPath);
    if (dryRun) {
      removed.push(relPath);
      continue;
    }
    try {
      rmSync(absPath, { recursive: true, force: true });
      removed.push(relPath);
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      failed.push({ path: relPath, message });
    }
  }

  return {
    rootDir,
    dryRun,
    includeNodeModules,
    removed,
    failed,
    scanned: targets,
  };
}

function parseArgs(argv) {
  let dryRun = false;
  let includeNodeModules = false;
  let format = 'text';
  let rootDir = process.cwd();

  for (const arg of argv.slice(2)) {
    if (arg === '--dry-run') {
      dryRun = true;
      continue;
    }
    if (arg === '--include-node-modules') {
      includeNodeModules = true;
      continue;
    }
    if (arg === '--json') {
      format = 'json';
      continue;
    }
    if (arg.startsWith('--root=')) {
      rootDir = path.resolve(arg.slice('--root='.length));
    }
  }

  return { dryRun, includeNodeModules, format, rootDir };
}

function renderText(summary) {
  const lines = [];
  lines.push('Root safe-remove cleanup');
  lines.push(`- root: ${summary.rootDir}`);
  lines.push(`- dryRun: ${summary.dryRun}`);
  lines.push(`- includeNodeModules: ${summary.includeNodeModules}`);
  lines.push(`- candidate files: ${summary.scanned.files.length}`);
  lines.push(`- candidate dirs: ${summary.scanned.dirs.length}`);
  lines.push(`- removed: ${summary.removed.length}`);
  lines.push(`- failed: ${summary.failed.length}`);

  if (summary.removed.length > 0) {
    lines.push('');
    lines.push('Removed targets:');
    for (const item of summary.removed) {
      lines.push(`- ${item}`);
    }
  }

  if (summary.failed.length > 0) {
    lines.push('');
    lines.push('Failed targets:');
    for (const item of summary.failed) {
      lines.push(`- ${item.path}: ${item.message}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

export function runRootSafeRemove(argv = process.argv) {
  const options = parseArgs(argv);
  const result = cleanRootSafeRemove(options.rootDir, {
    dryRun: options.dryRun,
    includeNodeModules: options.includeNodeModules,
  });
  const exitCode = result.failed.length > 0 ? 1 : 0;

  if (options.format === 'json') {
    process.stdout.write(JSON.stringify({ ...result, exitCode }, null, 2));
    process.stdout.write('\n');
  } else {
    process.stdout.write(renderText(result));
  }

  return { ...result, exitCode };
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
  const outcome = runRootSafeRemove(process.argv);
  process.exit(outcome.exitCode);
}
