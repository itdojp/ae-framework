#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';

const DEFAULT_REPO = process.env.GITHUB_REPOSITORY || 'itdojp/ae-framework';

function usage() {
  return `Usage: node scripts/codex/export-issue-task.mjs --issue <number> [options]

Export a GitHub Issue into a local Codex CLI task file.

Required:
  --issue <number>          GitHub Issue number to export.

Options:
  --repo <owner/name>       GitHub repository. Default: ${DEFAULT_REPO}
  --work <path>             Repository/worktree root. Default: current directory.
  --out <path>              Output file. Default: <work>/.codex-local/tasks/issue-<number>.md
  --gh <path>               gh executable. Default: gh
  --generated-at <iso>      Timestamp to write into task metadata. Default: current time.
  --no-preflight            Do not include the Context Pack preflight block.
  --print-commands          Print worktree and codex exec examples after writing.
  -h, --help                Show this help.

The output is local operator input. Keep it under .codex-local/tasks/ and do not stage it.`;
}

function readOption(argv, index, name) {
  const current = argv[index];
  if (current.startsWith(`${name}=`)) {
    return { value: current.slice(name.length + 1), nextIndex: index };
  }
  if (current === name && argv[index + 1]) {
    return { value: argv[index + 1], nextIndex: index + 1 };
  }
  return null;
}

function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    repo: DEFAULT_REPO,
    issue: null,
    work: process.cwd(),
    out: null,
    gh: 'gh',
    generatedAt: new Date().toISOString(),
    includePreflight: true,
    printCommands: false,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '-h' || arg === '--help') {
      options.help = true;
      continue;
    }
    if (arg === '--no-preflight') {
      options.includePreflight = false;
      continue;
    }
    if (arg === '--print-commands') {
      options.printCommands = true;
      continue;
    }
    const named = ['--repo', '--issue', '--work', '--out', '--gh', '--generated-at']
      .map((name) => [name, readOption(argv, index, name)])
      .find(([, result]) => result);
    if (named) {
      const [name, result] = named;
      if (name === '--repo') options.repo = result.value;
      if (name === '--issue') options.issue = result.value;
      if (name === '--work') options.work = result.value;
      if (name === '--out') options.out = result.value;
      if (name === '--gh') options.gh = result.value;
      if (name === '--generated-at') options.generatedAt = result.value;
      index = result.nextIndex;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  if (!options.help) {
    const issueNumber = Number(options.issue);
    if (!Number.isInteger(issueNumber) || issueNumber <= 0) {
      throw new Error('--issue must be a positive integer');
    }
    options.issue = issueNumber;
    options.repo = String(options.repo || '').trim();
    if (!/^[^/\s]+\/[^/\s]+$/.test(options.repo)) {
      throw new Error('--repo must be in owner/name form');
    }
  }

  return options;
}

function assertPathInside(parent, candidate) {
  const relative = path.relative(parent, candidate);
  if (relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative))) {
    return;
  }
  throw new Error(`output path must stay under work root: ${candidate}`);
}

function assertResolvedPathInside(parent, candidate, context) {
  const relative = path.relative(parent, candidate);
  if (relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative))) {
    return;
  }
  throw new Error(`${context} must stay under work root after resolving symlinks: ${candidate}`);
}

function realpathIfExists(candidate) {
  try {
    return fs.realpathSync.native(candidate);
  } catch (error) {
    if (error && error.code === 'ENOENT') {
      return null;
    }
    throw error;
  }
}

function lstatIfExists(candidate) {
  try {
    return fs.lstatSync(candidate);
  } catch (error) {
    if (error && error.code === 'ENOENT') {
      return null;
    }
    throw error;
  }
}

function nearestExistingAncestor(candidate) {
  let current = path.resolve(candidate);
  while (!fs.existsSync(current)) {
    const parent = path.dirname(current);
    if (parent === current) {
      throw new Error(`no existing ancestor found for output path: ${candidate}`);
    }
    current = parent;
  }
  return current;
}

function resolveOutputPath({ work, out, issue }) {
  const workRoot = path.resolve(work);
  const outputPath = out
    ? path.resolve(workRoot, out)
    : path.join(workRoot, '.codex-local', 'tasks', `issue-${issue}.md`);
  assertPathInside(workRoot, outputPath);
  return { workRoot, outputPath };
}

function ensureOutputPathSafeForWrite({ workRoot, outputPath }) {
  const realWorkRoot = fs.realpathSync.native(workRoot);
  const outputStat = lstatIfExists(outputPath);
  if (outputStat?.isSymbolicLink()) {
    throw new Error(`output file must not be a symbolic link: ${outputPath}`);
  }

  const existingOutput = realpathIfExists(outputPath);
  if (existingOutput) {
    assertResolvedPathInside(realWorkRoot, existingOutput, 'output file');
  }

  const outputDir = path.dirname(outputPath);
  const existingAncestor = nearestExistingAncestor(outputDir);
  const realExistingAncestor = fs.realpathSync.native(existingAncestor);
  assertResolvedPathInside(realWorkRoot, realExistingAncestor, 'output directory');

  fs.mkdirSync(outputDir, { recursive: true });
  const realOutputDir = fs.realpathSync.native(outputDir);
  assertResolvedPathInside(realWorkRoot, realOutputDir, 'output directory');

  const outputAfterMkdir = realpathIfExists(outputPath);
  if (outputAfterMkdir) {
    assertResolvedPathInside(realWorkRoot, outputAfterMkdir, 'output file');
  }
  const outputStatAfterMkdir = lstatIfExists(outputPath);
  if (outputStatAfterMkdir?.isSymbolicLink()) {
    throw new Error(`output file must not be a symbolic link: ${outputPath}`);
  }
}

function fetchIssue({ gh, repo, issue }) {
  const result = spawnSync(gh, [
    'issue',
    'view',
    String(issue),
    '--repo',
    repo,
    '--json',
    'title,body,url',
  ], {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });

  if (result.error) {
    throw new Error(`failed to execute gh: ${result.error.message}`);
  }
  if (result.status !== 0) {
    throw new Error(`gh issue view failed (${result.status}): ${result.stderr.trim()}`);
  }
  try {
    const issueJson = JSON.parse(result.stdout);
    return {
      title: String(issueJson.title || '').trim(),
      url: String(issueJson.url || '').trim(),
      body: String(issueJson.body || '').trimEnd(),
    };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`failed to parse gh issue view JSON: ${message}`);
  }
}

function contextPackPreflightBlock() {
  return `## Context Pack preflight

- Read \`AGENTS.md\`.
- Read \`docs/spec/context-pack.md\` and \`spec/context-pack/boundary-map.json\`.
- Identify the Context Pack \`objects\`, \`morphisms\`, \`diagrams\`, \`acceptance_tests\`, and existing tests relevant to the Issue target files.
- If the requested change conflicts with Context Pack constraints or the boundary map, stop before implementation and record \`Context Pack conflict: found\` with the conflicting IDs/paths in the PR or Issue comment.
- If no conflict is found, record \`Context Pack conflict: none\` in the PR body.
- Do not promote routine changes to MBT, property, or formal lanes unless the Issue, risk label, assurance profile, or critical-core boundary requires it.`;
}

function formatTaskMarkdown({
  issue,
  repo,
  title,
  url,
  body,
  generatedAt,
  includePreflight = true,
}) {
  const sections = [
    `# ${title}`,
    [
      `Issue: ${url}`,
      `Repository: ${repo}`,
      `Issue number: ${issue}`,
      `Exported at: ${generatedAt}`,
      '',
      'Local task file: do not stage or commit this file. Keep it under `.codex-local/tasks/`.',
    ].join('\n'),
  ];
  if (includePreflight) {
    sections.push(contextPackPreflightBlock());
  }
  sections.push('## Issue body', body);
  return `${sections.join('\n\n')}\n`;
}

function shellQuote(value) {
  return `'${String(value).replace(/'/g, "'\\''")}'`;
}

function commandExamples({ issue, workRoot, outputPath }) {
  const sibling = path.join(path.dirname(workRoot), `ae-framework-${issue}-work`);
  return [
    '# Dedicated worktree example',
    'git fetch origin main --prune',
    `git worktree add ${shellQuote(sibling)} -b ${shellQuote(`work/issue-${issue}`)} origin/main`,
    '',
    '# Preflight reminder',
    '# Read the Context Pack preflight block in the task file before implementation.',
    '# If constraints conflict, stop and record "Context Pack conflict: found".',
    '',
    '# Non-interactive Codex CLI example',
    `codex exec --cd ${shellQuote(sibling)} --sandbox workspace-write --ask-for-approval never - < ${shellQuote(outputPath)}`,
  ].join('\n');
}

function run(options = parseArgs()) {
  if (options.help) {
    process.stdout.write(`${usage()}\n`);
    return null;
  }
  const { workRoot, outputPath } = resolveOutputPath(options);
  const issue = fetchIssue(options);
  if (!issue.title || !issue.url) {
    throw new Error('gh issue view did not return title and url');
  }
  const task = formatTaskMarkdown({
    issue: options.issue,
    repo: options.repo,
    title: issue.title,
    url: issue.url,
    body: issue.body,
    generatedAt: options.generatedAt,
    includePreflight: options.includePreflight,
  });
  ensureOutputPathSafeForWrite({ workRoot, outputPath });
  fs.writeFileSync(outputPath, task, 'utf8');
  process.stdout.write(`[codex-issue-task] wrote ${outputPath}\n`);
  process.stdout.write(`[codex-issue-task] source ${issue.url}\n`);
  process.stdout.write('[codex-issue-task] do not stage .codex-local/tasks/ files\n');
  if (options.printCommands) {
    process.stdout.write(`\n${commandExamples({ issue: options.issue, workRoot, outputPath })}\n`);
  }
  return { outputPath, issue };
}

function isDirectExecution() {
  const entry = process.argv[1];
  return Boolean(entry) && import.meta.url === pathToFileURL(path.resolve(entry)).href;
}

if (isDirectExecution()) {
  try {
    run();
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`[codex-issue-task] ${message}\n`);
    process.exit(1);
  }
}

export {
  commandExamples,
  contextPackPreflightBlock,
  ensureOutputPathSafeForWrite,
  fetchIssue,
  formatTaskMarkdown,
  lstatIfExists,
  parseArgs,
  resolveOutputPath,
  run,
  usage,
};
