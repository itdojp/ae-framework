#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import process from 'node:process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export function parseArgs(argv = process.argv) {
  const options = {
    baseRef: 'origin/main',
    baseSha: '',
    fetchMissing: false,
    rootDir: process.cwd(),
    unknown: [],
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    if (arg === '--base-ref') {
      if (!next || next.startsWith('-')) {
        options.unknown.push(arg);
      } else {
        options.baseRef = next;
        index += 1;
      }
      continue;
    }
    if (arg.startsWith('--base-ref=')) {
      options.baseRef = arg.slice('--base-ref='.length);
      continue;
    }
    if (arg === '--base-sha') {
      if (!next || next.startsWith('-')) {
        options.unknown.push(arg);
      } else {
        options.baseSha = next;
        index += 1;
      }
      continue;
    }
    if (arg.startsWith('--base-sha=')) {
      options.baseSha = arg.slice('--base-sha='.length);
      continue;
    }
    if (arg === '--fetch-missing') {
      options.fetchMissing = true;
      continue;
    }
    if (arg === '--') {
      continue;
    }
    options.unknown.push(arg);
  }

  return options;
}

export function parseChangedMarkdownOutput(raw) {
  return String(raw ?? '')
    .split(/\r?\n/u)
    .map((line) => line.trim())
    .filter((line) => line.endsWith('.md'));
}

export function resolveBaseTarget(options) {
  return options.baseSha || options.baseRef;
}

export function isCommitAvailable(rootDir, commitish) {
  if (!commitish) {
    return false;
  }
  try {
    execFileSync('git', ['cat-file', '-e', `${commitish}^{commit}`], {
      cwd: rootDir,
      stdio: 'ignore',
    });
    return true;
  } catch {
    return false;
  }
}

export function fetchBaseSha(rootDir, baseSha) {
  execFileSync('git', ['fetch', '--no-tags', '--depth=1', 'origin', baseSha], {
    cwd: rootDir,
    stdio: 'inherit',
  });
}

export function listChangedMarkdown(rootDir, baseTarget) {
  const stdout = execFileSync(
    'git',
    ['diff', '--name-only', baseTarget, 'HEAD', '--', '*.md', '**/*.md'],
    { cwd: rootDir, encoding: 'utf8' },
  );
  return parseChangedMarkdownOutput(stdout);
}

export function runDoctest(rootDir, files) {
  execFileSync('pnpm', ['-s', 'tsx', 'scripts/doctest.ts', ...files], {
    cwd: rootDir,
    stdio: 'inherit',
    env: { ...process.env, DOCTEST_ENFORCE: process.env.DOCTEST_ENFORCE || '1' },
  });
}

export function main(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.unknown.length > 0) {
    throw new Error(`unknown arguments: ${options.unknown.join(', ')}`);
  }

  const baseTarget = resolveBaseTarget(options);
  if (!baseTarget) {
    throw new Error('base target is required');
  }

  if (options.baseSha && options.fetchMissing && !isCommitAvailable(options.rootDir, options.baseSha)) {
    fetchBaseSha(options.rootDir, options.baseSha);
  }

  const files = listChangedMarkdown(options.rootDir, baseTarget);
  if (files.length === 0) {
    process.stdout.write('No changed markdown files detected.\n');
    return 0;
  }

  process.stdout.write(`Running doctest for ${files.length} changed markdown file(s).\n`);
  runDoctest(options.rootDir, files);
  return 0;
}

export function isExecutedAsMain(metaUrl, argvPath = process.argv[1]) {
  if (!argvPath || typeof argvPath !== 'string') {
    return false;
  }
  try {
    return path.resolve(fileURLToPath(metaUrl)) === path.resolve(argvPath);
  } catch {
    return false;
  }
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  process.exit(main(process.argv));
}
