#!/usr/bin/env node

import { existsSync, readdirSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const TODO_MARKER_REGEX = /^\s*(?:#{1,6}\s+|[-*+]\s+|\d+\.\s+)?(?:\*\*)?(TODO|FIXME)(?!\/)(?:\*\*)?(.*)$/iu;
const TODO_ISSUE_REFERENCE_REGEX = /\b(?:TODO|FIXME)\s*\(\s*#\d+\s*\)/iu;
const DEFAULT_DOC_DIR = 'docs/ci';

function parseCsv(value) {
  return value
    .split(',')
    .map((entry) => entry.trim())
    .filter(Boolean);
}

export function parseArgs(argv = process.argv) {
  const options = {
    rootDir: process.cwd(),
    docs: [],
    docsProvided: false,
    format: 'text',
    unknown: [],
    help: false,
  };

  const docs = [];
  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg.startsWith('--root=')) {
      options.rootDir = path.resolve(arg.slice('--root='.length));
      continue;
    }
    if (arg === '--root') {
      const next = argv[index + 1];
      if (!next || next.startsWith('-')) {
        options.unknown.push(arg);
      } else {
        options.rootDir = path.resolve(next);
        index += 1;
      }
      continue;
    }
    if (arg.startsWith('--docs=')) {
      const value = arg.slice('--docs='.length);
      if (!value) {
        options.unknown.push(arg);
      } else {
        docs.push(...parseCsv(value));
      }
      continue;
    }
    if (arg === '--docs') {
      const next = argv[index + 1];
      if (!next || next.startsWith('-')) {
        options.unknown.push(arg);
      } else {
        docs.push(...parseCsv(next));
        index += 1;
      }
      continue;
    }
    if (arg.startsWith('--format=')) {
      const value = arg.slice('--format='.length);
      if (value === 'json' || value === 'text') {
        options.format = value;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    if (arg === '--format') {
      const next = argv[index + 1];
      if (next === 'json' || next === 'text') {
        options.format = next;
        index += 1;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    options.unknown.push(arg);
  }

  if (docs.length > 0) {
    options.docs = docs;
    options.docsProvided = true;
  }
  return options;
}

function listDefaultDocs(rootDir) {
  const docsDir = path.join(rootDir, DEFAULT_DOC_DIR);
  if (!existsSync(docsDir)) {
    return [];
  }
  return readdirSync(docsDir)
    .filter((entry) => entry.endsWith('.md'))
    .map((entry) => path.posix.join(DEFAULT_DOC_DIR, entry))
    .sort((a, b) => a.localeCompare(b));
}

export function collectTodoMarkerViolations(markdownPath, content) {
  const violations = [];
  const lines = content.split(/\r?\n/u);
  let inFence = false;

  for (let lineNumber = 0; lineNumber < lines.length; lineNumber += 1) {
    const line = lines[lineNumber];
    const trimmed = line.trim();
    if (trimmed.startsWith('```')) {
      inFence = !inFence;
      continue;
    }
    if (inFence) {
      continue;
    }
    if (!TODO_MARKER_REGEX.test(line)) {
      continue;
    }
    if (TODO_ISSUE_REFERENCE_REGEX.test(line)) {
      continue;
    }
    violations.push({
      markdownPath,
      line: lineNumber + 1,
      content: line.trim(),
      message: 'TODO/FIXME markers in docs/ci must include issue references: TODO(#<issue>) or FIXME(#<issue>)',
    });
  }

  return violations;
}

function renderText(result) {
  const lines = [];
  lines.push('Doc TODO marker check');
  lines.push(`- docs scanned: ${result.docsScanned.length}`);
  lines.push(`- missing docs: ${result.missingDocs.length}`);
  lines.push(`- violations: ${result.violations.length}`);
  if (result.missingDocs.length > 0) {
    lines.push('', 'Missing docs:');
    for (const finding of result.missingDocs) {
      lines.push(`- ${finding.markdownPath}: ${finding.message}`);
    }
  }
  if (result.violations.length > 0) {
    lines.push('', 'Violations:');
    for (const finding of result.violations) {
      lines.push(`- ${finding.markdownPath}:${finding.line} -> ${finding.content}`);
    }
  }
  return `${lines.join('\n')}\n`;
}

export function runDocTodoMarkerCheck(argv = process.argv) {
  const options = parseArgs(argv);
  const docsToScan = options.docsProvided ? options.docs : listDefaultDocs(options.rootDir);
  if (options.help) {
    return {
      ...options,
      docs: docsToScan,
      docsScanned: [],
      missingDocs: [],
      violations: [],
      exitCode: 0,
      help: true,
    };
  }
  if (options.unknown.length > 0) {
    return {
      ...options,
      docs: docsToScan,
      docsScanned: [],
      missingDocs: [],
      violations: [],
      exitCode: 2,
      help: false,
    };
  }

  const docsScanned = [];
  const missingDocs = [];
  const violations = [];

  for (const markdownPath of docsToScan) {
    const absolutePath = path.resolve(options.rootDir, markdownPath);
    if (!existsSync(absolutePath)) {
      missingDocs.push({
        markdownPath,
        message: 'document file is missing',
      });
      continue;
    }
    docsScanned.push(markdownPath);
    const content = readFileSync(absolutePath, 'utf8');
    violations.push(...collectTodoMarkerViolations(markdownPath, content));
  }

  const exitCode = missingDocs.length > 0 || violations.length > 0 ? 1 : 0;
  return {
    ...options,
    docs: docsToScan,
    docsScanned,
    missingDocs,
    violations,
    exitCode,
    help: false,
  };
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

function printHelp() {
  console.log(`Usage: node scripts/docs/check-doc-todo-markers.mjs [options]

Options:
  --docs <file1,file2>   Comma separated markdown files to inspect
  --root <dir>           Repository root directory (default: current directory)
  --format <text|json>   Output format (default: text)
  -h, --help             Show this help
`);
}

function main(argv = process.argv) {
  const result = runDocTodoMarkerCheck(argv);
  if (result.help) {
    printHelp();
    return 0;
  }
  if (result.unknown.length > 0) {
    console.error(`Unknown argument(s): ${result.unknown.join(', ')}`);
    printHelp();
    return 2;
  }
  if (result.format === 'json') {
    process.stdout.write(`${JSON.stringify({
      docsScanned: result.docsScanned,
      missingDocs: result.missingDocs,
      violations: result.violations,
      exitCode: result.exitCode,
    }, null, 2)}\n`);
  } else {
    process.stdout.write(renderText(result));
  }
  return result.exitCode;
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  process.exitCode = main(process.argv);
}
