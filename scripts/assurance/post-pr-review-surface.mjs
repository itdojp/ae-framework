#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';

const DEFAULT_MODE = 'dry-run';
const DEFAULT_MARKER = '<!-- ae-assurance-review-surface -->';
const DEFAULT_TEMP_DIR = '.codex-local/tmp/pr-review-surface-comments';
const MODES = new Set(['dry-run', 'comment']);

function usage() {
  process.stdout.write(`Usage: node scripts/assurance/post-pr-review-surface.mjs [options]\n\nOptions:\n  --repo <owner/repo>       GitHub repository that owns the PR.\n  --pr <number>             Pull request number.\n  --body-file <path>        Generated reviewer-surface Markdown to post.\n  --mode <dry-run|comment>  dry-run prints the target/comment body; comment calls gh pr comment (default: ${DEFAULT_MODE}).\n  --marker <text>           Marker prepended to the posted comment body (default: ${DEFAULT_MARKER}).\n  --gh-bin <path>           gh executable for comment mode (default: gh).\n  --help                    Show this help.\n\nThe helper never approves, reviews, merges, or rewrites the Markdown source file. It only posts a PR comment in --mode comment.\n`);
}

function readRequiredValue(argv, index, flag) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`${flag} requires a value`);
  }
  return next;
}

function parsePositiveInteger(value, flag) {
  const raw = String(value ?? '').trim();
  if (!/^[1-9]\d*$/u.test(raw)) {
    throw new Error(`${flag} must be a positive integer: ${value}`);
  }
  const parsed = Number.parseInt(raw, 10);
  if (!Number.isFinite(parsed) || parsed < 1) {
    throw new Error(`${flag} must be a positive integer: ${value}`);
  }
  return parsed;
}

function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    repo: null,
    pr: null,
    bodyFile: null,
    mode: DEFAULT_MODE,
    marker: DEFAULT_MARKER,
    ghBin: 'gh',
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--repo') {
      options.repo = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--pr') {
      options.pr = parsePositiveInteger(readRequiredValue(argv, index, arg), arg);
      index += 1;
      continue;
    }
    if (arg === '--body-file') {
      options.bodyFile = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--mode') {
      options.mode = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--marker') {
      options.marker = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--gh-bin') {
      options.ghBin = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (options.help) return options;
  validateOptions(options);
  return options;
}

function validateOptions(options) {
  if (!options.repo || !/^[^/\s]+\/[^/\s]+$/u.test(options.repo)) {
    throw new Error('--repo must be owner/name');
  }
  if (!Number.isInteger(options.pr) || options.pr < 1) {
    throw new Error('--pr must be a positive integer');
  }
  if (!options.bodyFile) {
    throw new Error('--body-file is required');
  }
  if (!MODES.has(options.mode)) {
    throw new Error(`--mode must be one of: ${[...MODES].join(', ')}`);
  }
  if (!String(options.marker ?? '').trim()) {
    throw new Error('--marker must not be empty');
  }
}

function toPosixPath(filePath) {
  return filePath.split(path.sep).join('/');
}

function toDisplayPath(filePath) {
  const resolved = path.resolve(filePath);
  const relative = path.relative(process.cwd(), resolved);
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) {
    return toPosixPath(filePath);
  }
  return toPosixPath(relative);
}

function readBodyFile(filePath) {
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) {
    throw new Error(`--body-file does not exist: ${toDisplayPath(filePath)}`);
  }
  const stats = fs.statSync(resolved);
  if (!stats.isFile()) {
    throw new Error(`--body-file must be a file: ${toDisplayPath(filePath)}`);
  }
  const body = fs.readFileSync(resolved, 'utf8');
  if (body.trim().length === 0) {
    throw new Error(`--body-file must not be empty: ${toDisplayPath(filePath)}`);
  }
  return body;
}

function buildCommentBody(body, marker) {
  const normalizedBody = body.endsWith('\n') ? body : `${body}\n`;
  return `${marker}\n\n${normalizedBody}`;
}

function renderDryRun(options, commentBody) {
  return [
    '[assurance-review-surface-post] dry-run',
    `repo: ${options.repo}`,
    `pr: ${options.pr}`,
    `bodyFile: ${toDisplayPath(options.bodyFile)}`,
    `marker: ${options.marker}`,
    'mode: dry-run',
    '',
    '--- comment body ---',
    commentBody,
  ].join('\n');
}

function writeTempCommentBody(commentBody) {
  const tempDir = path.resolve(DEFAULT_TEMP_DIR);
  fs.mkdirSync(tempDir, { recursive: true });
  const filePath = path.join(tempDir, `assurance-review-${process.pid}-${Date.now()}.md`);
  fs.writeFileSync(filePath, commentBody, 'utf8');
  return filePath;
}

function runGhComment(options, commentBody) {
  const commentFile = writeTempCommentBody(commentBody);
  try {
    const result = spawnSync(options.ghBin, [
      'pr',
      'comment',
      String(options.pr),
      '--repo',
      options.repo,
      '--body-file',
      commentFile,
    ], {
      cwd: process.cwd(),
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    });

    if (result.error) {
      throw new Error(`failed to execute ${options.ghBin}: ${result.error.message}`);
    }
    if (result.status !== 0) {
      const stderr = result.stderr.trim() || '(empty)';
      throw new Error(`gh pr comment failed; ensure gh is installed and authenticated (run gh auth login, or set GH_TOKEN with repo access). stderr: ${stderr}`);
    }
    return result.stdout.trim();
  } finally {
    fs.rmSync(commentFile, { force: true });
  }
}

function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    usage();
    return 0;
  }
  const sourceBody = readBodyFile(options.bodyFile);
  const commentBody = buildCommentBody(sourceBody, options.marker);
  if (options.mode === 'dry-run') {
    process.stdout.write(`${renderDryRun(options, commentBody)}\n`);
    return 0;
  }
  const ghOutput = runGhComment(options, commentBody);
  process.stdout.write([
    '[assurance-review-surface-post] posted',
    `repo: ${options.repo}`,
    `pr: ${options.pr}`,
    `bodyFile: ${toDisplayPath(options.bodyFile)}`,
    `marker: ${options.marker}`,
    ghOutput ? `gh: ${ghOutput}` : null,
  ].filter(Boolean).join('\n') + '\n');
  return 0;
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  try {
    process.exitCode = run();
  } catch (error) {
    process.stderr.write(`[assurance-review-surface-post] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}

export {
  buildCommentBody,
  parseArgs,
  run,
};
