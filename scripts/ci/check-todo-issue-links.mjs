#!/usr/bin/env node

import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const TODO_ISSUE_PATTERN = /\b(TODO|FIXME)\s*\(\s*#(\d+)\s*\)/gu;
const DEFAULT_INCLUDE_PREFIXES = ['src/', 'scripts/', 'docs/', 'tests/', 'spec/', 'README.md'];

/**
 * Parse TODO/FIXME issue references from text.
 *
 * @param {string} content
 * @param {string} filePath
 * @returns {Array<{file: string, line: number, column: number, marker: string, issue: number}>}
 */
export function parseTodoIssueReferences(content, filePath) {
  const references = [];
  const lines = content.split(/\r?\n/u);

  for (let lineIndex = 0; lineIndex < lines.length; lineIndex += 1) {
    const line = lines[lineIndex];
    TODO_ISSUE_PATTERN.lastIndex = 0;
    let match = TODO_ISSUE_PATTERN.exec(line);
    while (match) {
      const marker = match[1] ?? 'TODO';
      const issueNumber = Number.parseInt(match[2] ?? '', 10);
      if (Number.isFinite(issueNumber) && issueNumber > 0) {
        references.push({
          file: filePath,
          line: lineIndex + 1,
          column: match.index + 1,
          marker,
          issue: issueNumber,
        });
      }
      match = TODO_ISSUE_PATTERN.exec(line);
    }
  }

  return references;
}

/**
 * @param {Array<{file: string, line: number, column: number, marker: string, issue: number}>} references
 * @returns {Map<number, Array<{file: string, line: number, column: number, marker: string, issue: number}>>}
 */
export function buildIssueReferenceMap(references) {
  const byIssue = new Map();
  for (const reference of references) {
    const current = byIssue.get(reference.issue);
    if (current) {
      current.push(reference);
    } else {
      byIssue.set(reference.issue, [reference]);
    }
  }
  return byIssue;
}

/**
 * @param {Map<number, Array<{file: string, line: number, column: number, marker: string, issue: number}>>} referenceMap
 * @param {Map<number, {state: 'open' | 'closed' | 'missing', url?: string}>} issueStates
 * @param {{allowIssues?: number[]}} [options]
 */
export function evaluateIssueReferenceMap(referenceMap, issueStates, options = {}) {
  const allowed = new Set(options.allowIssues ?? []);
  const issues = [...referenceMap.keys()].sort((a, b) => a - b);
  const closed = [];
  const missing = [];
  const unresolved = [];

  for (const issue of issues) {
    if (allowed.has(issue)) {
      continue;
    }
    const state = issueStates.get(issue);
    if (!state) {
      unresolved.push({ issue, occurrences: referenceMap.get(issue) ?? [] });
      continue;
    }

    if (state.state === 'closed') {
      closed.push({ issue, occurrences: referenceMap.get(issue) ?? [], url: state.url });
      continue;
    }
    if (state.state === 'missing') {
      missing.push({ issue, occurrences: referenceMap.get(issue) ?? [], url: state.url });
    }
  }

  return {
    closed,
    missing,
    unresolved,
    violations: [...closed, ...missing, ...unresolved],
  };
}

function parseArgs(argv) {
  let mode = 'strict';
  let format = 'text';
  let rootDir = process.cwd();
  let repository = process.env.GITHUB_REPOSITORY ?? '';
  const includePrefixes = [];
  const allowIssues = [];
  let token = process.env.GITHUB_TOKEN || process.env.GH_TOKEN || '';

  for (const arg of argv.slice(2)) {
    if (arg.startsWith('--mode=')) {
      const value = arg.slice('--mode='.length);
      if (value === 'strict' || value === 'warn') {
        mode = value;
      }
      continue;
    }
    if (arg.startsWith('--format=')) {
      const value = arg.slice('--format='.length);
      if (value === 'json' || value === 'text') {
        format = value;
      }
      continue;
    }
    if (arg.startsWith('--root=')) {
      rootDir = path.resolve(arg.slice('--root='.length));
      continue;
    }
    if (arg.startsWith('--repo=')) {
      repository = arg.slice('--repo='.length).trim();
      continue;
    }
    if (arg.startsWith('--include=')) {
      const value = arg.slice('--include='.length).trim();
      if (value) {
        includePrefixes.push(value);
      }
      continue;
    }
    if (arg.startsWith('--allow-issue=')) {
      const value = Number.parseInt(arg.slice('--allow-issue='.length), 10);
      if (Number.isFinite(value) && value > 0) {
        allowIssues.push(value);
      }
      continue;
    }
    if (arg.startsWith('--token=')) {
      token = arg.slice('--token='.length).trim();
    }
  }

  return {
    mode,
    format,
    rootDir,
    repository,
    includePrefixes: includePrefixes.length > 0 ? includePrefixes : DEFAULT_INCLUDE_PREFIXES,
    allowIssues,
    token,
  };
}

function listTrackedFiles(rootDir) {
  const output = execFileSync('git', ['-C', rootDir, 'ls-files', '-z'], {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  return output.split('\0').filter(Boolean);
}

function selectTargetFiles(files, prefixes) {
  const sortedPrefixes = [...prefixes].sort((a, b) => a.localeCompare(b));
  return files.filter((file) => sortedPrefixes.some((prefix) => file === prefix || file.startsWith(prefix)));
}

/**
 * @param {string} repository
 * @returns {{owner: string, repo: string}}
 */
function splitRepository(repository) {
  const [owner, repo] = repository.split('/');
  if (!owner || !repo) {
    throw new Error('repository must be in <owner>/<repo> format');
  }
  return { owner, repo };
}

/**
 * @param {number} issue
 * @param {{owner: string, repo: string, token: string, fetchImpl: typeof fetch}} context
 * @returns {Promise<{state: 'open' | 'closed' | 'missing', url?: string}>}
 */
async function fetchIssueState(issue, context) {
  const { owner, repo, token, fetchImpl } = context;
  const url = `https://api.github.com/repos/${owner}/${repo}/issues/${issue}`;
  const headers = {
    Accept: 'application/vnd.github+json',
    'User-Agent': 'ae-framework-todo-link-check',
  };
  if (token) {
    headers.Authorization = `Bearer ${token}`;
  }

  const response = await fetchImpl(url, { headers });
  if (response.status === 404) {
    return { state: 'missing', url };
  }
  if (!response.ok) {
    const text = await response.text();
    const body = text.replace(/\s+/gu, ' ').trim().slice(0, 200);
    throw new Error(`GitHub API request failed for #${issue}: HTTP ${response.status}${body ? ` (${body})` : ''}`);
  }

  const data = await response.json();
  const state = data?.state === 'closed' ? 'closed' : 'open';
  return { state, url: data?.html_url || url };
}

/**
 * @param {number[]} issueNumbers
 * @param {{repository: string, token: string, fetchImpl: typeof fetch}} options
 * @returns {Promise<Map<number, {state: 'open' | 'closed' | 'missing', url?: string}>>}
 */
export async function fetchIssueStates(issueNumbers, options) {
  const { repository, token, fetchImpl } = options;
  const context = { ...splitRepository(repository), token, fetchImpl };
  const states = new Map();
  for (const issue of issueNumbers) {
    // Sequential requests keep behavior predictable and avoid burst traffic to the GitHub API.
    // eslint-disable-next-line no-await-in-loop
    states.set(issue, await fetchIssueState(issue, context));
  }
  return states;
}

/**
 * @param {Array<{file: string, line: number, column: number, marker: string, issue: number}>} references
 * @param {Map<number, {state: 'open' | 'closed' | 'missing', url?: string}>} issueStates
 * @param {{allowIssues: number[]}} options
 */
function buildReport(references, issueStates, options) {
  const referenceMap = buildIssueReferenceMap(references);
  const evaluation = evaluateIssueReferenceMap(referenceMap, issueStates, options);
  const uniqueIssueCount = referenceMap.size;
  const checkedIssueCount = uniqueIssueCount - new Set(options.allowIssues).size;
  return {
    references,
    issueStates,
    referenceMap,
    evaluation,
    summary: {
      references: references.length,
      uniqueIssues: uniqueIssueCount,
      checkedIssues: Math.max(checkedIssueCount, 0),
      closedIssues: evaluation.closed.length,
      missingIssues: evaluation.missing.length,
      unresolvedIssues: evaluation.unresolved.length,
    },
  };
}

function renderText(result, options) {
  const lines = [];
  lines.push('TODO/FIXME issue reference check');
  lines.push(`- mode: ${options.mode}`);
  lines.push(`- root: ${options.rootDir}`);
  lines.push(`- repo: ${options.repository || '(unset)'}`);
  lines.push(`- include: ${options.includePrefixes.join(', ')}`);
  lines.push(`- scanned files: ${result.scannedFiles}`);
  lines.push(`- references: ${result.report.summary.references}`);
  lines.push(`- unique issues: ${result.report.summary.uniqueIssues}`);
  lines.push(`- closed issue refs: ${result.report.summary.closedIssues}`);
  lines.push(`- missing issue refs: ${result.report.summary.missingIssues}`);
  lines.push(`- unresolved issue refs: ${result.report.summary.unresolvedIssues}`);
  lines.push(`- api error: ${result.apiError ? result.apiError : 'none'}`);

  if (result.report.evaluation.closed.length > 0) {
    lines.push('');
    lines.push('Closed issue references:');
    for (const item of result.report.evaluation.closed) {
      const locations = item.occurrences
        .slice(0, 8)
        .map((entry) => `${entry.file}:${entry.line}`)
        .join(', ');
      lines.push(`- #${item.issue}: ${locations}`);
    }
  }

  if (result.report.evaluation.missing.length > 0) {
    lines.push('');
    lines.push('Missing issue references:');
    for (const item of result.report.evaluation.missing) {
      const locations = item.occurrences
        .slice(0, 8)
        .map((entry) => `${entry.file}:${entry.line}`)
        .join(', ');
      lines.push(`- #${item.issue}: ${locations}`);
    }
  }

  if (result.report.evaluation.unresolved.length > 0) {
    lines.push('');
    lines.push('Unresolved issue references:');
    for (const item of result.report.evaluation.unresolved) {
      const locations = item.occurrences
        .slice(0, 8)
        .map((entry) => `${entry.file}:${entry.line}`)
        .join(', ');
      lines.push(`- #${item.issue}: ${locations}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

/**
 * @param {string[]} [argv]
 * @param {{fetchImpl?: typeof fetch}} [runtime]
 */
export async function runTodoIssueLinkCheck(argv = process.argv, runtime = {}) {
  const options = parseArgs(argv);
  const fetchImpl = runtime.fetchImpl ?? globalThis.fetch;
  const outcome = {
    options,
    scannedFiles: 0,
    report: {
      references: [],
      issueStates: new Map(),
      referenceMap: new Map(),
      evaluation: { closed: [], missing: [], unresolved: [], violations: [] },
      summary: { references: 0, uniqueIssues: 0, checkedIssues: 0, closedIssues: 0, missingIssues: 0, unresolvedIssues: 0 },
    },
    apiError: '',
    exitCode: 0,
  };

  let trackedFiles = [];
  try {
    trackedFiles = listTrackedFiles(options.rootDir);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    outcome.apiError = `failed to list tracked files: ${message}`;
    outcome.exitCode = options.mode === 'warn' ? 0 : 1;
    return outcome;
  }

  const files = selectTargetFiles(trackedFiles, options.includePrefixes);
  outcome.scannedFiles = files.length;

  const references = [];
  for (const file of files) {
    const absolutePath = path.join(options.rootDir, file);
    let content;
    try {
      content = readFileSync(absolutePath, 'utf8');
    } catch {
      continue;
    }
    references.push(...parseTodoIssueReferences(content, file));
  }

  const issueNumbers = [...new Set(references.map((entry) => entry.issue))].sort((a, b) => a - b);
  let issueStates = new Map();
  if (issueNumbers.length > 0) {
    if (!options.repository) {
      outcome.apiError = 'GITHUB_REPOSITORY is required when TODO/FIXME issue references are present';
    } else if (typeof fetchImpl !== 'function') {
      outcome.apiError = 'fetch implementation is not available';
    } else {
      try {
        issueStates = await fetchIssueStates(issueNumbers, {
          repository: options.repository,
          token: options.token,
          fetchImpl,
        });
      } catch (error) {
        outcome.apiError = error instanceof Error ? error.message : String(error);
      }
    }
  }

  outcome.report = buildReport(references, issueStates, { allowIssues: options.allowIssues });

  if (outcome.apiError) {
    outcome.exitCode = options.mode === 'warn' ? 0 : 1;
  } else if (outcome.report.evaluation.violations.length > 0) {
    outcome.exitCode = options.mode === 'warn' ? 0 : 1;
  } else {
    outcome.exitCode = 0;
  }

  if (options.format === 'json') {
    const json = {
      mode: options.mode,
      root: options.rootDir,
      repository: options.repository,
      includePrefixes: options.includePrefixes,
      allowIssues: options.allowIssues,
      scannedFiles: outcome.scannedFiles,
      summary: outcome.report.summary,
      apiError: outcome.apiError || null,
      closed: outcome.report.evaluation.closed,
      missing: outcome.report.evaluation.missing,
      unresolved: outcome.report.evaluation.unresolved,
      exitCode: outcome.exitCode,
    };
    process.stdout.write(`${JSON.stringify(json, null, 2)}\n`);
  } else {
    process.stdout.write(renderText(outcome, options));
  }

  return outcome;
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
  runTodoIssueLinkCheck(process.argv)
    .then((result) => {
      process.exit(result.exitCode);
    })
    .catch((error) => {
      const message = error instanceof Error ? error.message : String(error);
      process.stderr.write(`check-todo-issue-links failed: ${message}\n`);
      process.exit(1);
    });
}
