#!/usr/bin/env node

import { spawnSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const DEFAULT_RUNBOOK_FILES = [
  'docs/ci/ci-troubleshooting-guide.md',
  'docs/ci/pr-automation.md',
  'docs/ci/copilot-review-gate.md',
  'docs/ci/copilot-auto-fix.md',
  'docs/ci/auto-merge.md',
];

const SUPPORTED_SHELL_LANGS = new Set(['bash', 'sh', 'shell', 'zsh']);

function parseCsv(value) {
  return value
    .split(',')
    .map((entry) => entry.trim())
    .filter(Boolean);
}

export function parseArgs(argv = process.argv) {
  const options = {
    rootDir: process.cwd(),
    docs: [...DEFAULT_RUNBOOK_FILES],
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
      if (value.length === 0) {
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

export function extractShellBlocks(markdownContent) {
  const lines = markdownContent.split(/\r?\n/u);
  const blocks = [];
  let inFence = false;
  let fenceLang = '';
  let fenceStartLine = 0;
  let buffer = [];

  for (let lineNumber = 0; lineNumber < lines.length; lineNumber += 1) {
    const line = lines[lineNumber];
    const trimmed = line.trim();
    if (trimmed.startsWith('```')) {
      if (!inFence) {
        inFence = true;
        fenceLang = trimmed.slice(3).trim().toLowerCase();
        fenceStartLine = lineNumber + 1;
        buffer = [];
      } else {
        if (SUPPORTED_SHELL_LANGS.has(fenceLang)) {
          blocks.push({
            startLine: fenceStartLine,
            language: fenceLang || 'bash',
            content: buffer.join('\n'),
          });
        }
        inFence = false;
        fenceLang = '';
        fenceStartLine = 0;
        buffer = [];
      }
      continue;
    }
    if (inFence) {
      buffer.push(line);
    }
  }

  return blocks;
}

function sanitizeShellSnippet(content) {
  return content.replace(/<[^>\n]+>/gu, 'PLACEHOLDER');
}

export function validateShellSyntax(content) {
  const validation = spawnSync('bash', ['-n'], {
    encoding: 'utf8',
    stdio: ['pipe', 'pipe', 'pipe'],
    input: sanitizeShellSnippet(content),
  });
  if (validation.error) {
    const message = validation.error instanceof Error ? validation.error.message : String(validation.error);
    return {
      ok: false,
      message,
    };
  }
  return {
    ok: validation.status === 0,
    message: (validation.stderr || validation.stdout || '').trim(),
  };
}

function renderText(result) {
  const lines = [];
  lines.push('Runbook command block check');
  lines.push(`- docs scanned: ${result.docsScanned.length}`);
  lines.push(`- missing docs: ${result.missingDocs.length}`);
  lines.push(`- shell blocks: ${result.shellBlocksScanned}`);
  lines.push(`- syntax errors: ${result.syntaxErrors.length}`);
  if (result.missingDocs.length > 0) {
    lines.push('', 'Missing docs:');
    for (const finding of result.missingDocs) {
      lines.push(`- ${finding.markdownPath}: ${finding.message}`);
    }
  }
  if (result.syntaxErrors.length > 0) {
    lines.push('', 'Syntax errors:');
    for (const finding of result.syntaxErrors) {
      lines.push(`- ${finding.markdownPath}:${finding.line} -> ${finding.message}`);
    }
  }
  return `${lines.join('\n')}\n`;
}

export function runRunbookCommandCheck(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    return {
      ...options,
      docsScanned: [],
      missingDocs: [],
      shellBlocksScanned: 0,
      syntaxErrors: [],
      exitCode: 0,
      help: true,
    };
  }
  if (options.unknown.length > 0) {
    return {
      ...options,
      docsScanned: [],
      missingDocs: [],
      shellBlocksScanned: 0,
      syntaxErrors: [],
      exitCode: 2,
      help: false,
    };
  }

  const docsScanned = [];
  const missingDocs = [];
  const syntaxErrors = [];
  let shellBlocksScanned = 0;

  for (const markdownPath of options.docs) {
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
    const blocks = extractShellBlocks(content);
    shellBlocksScanned += blocks.length;
    for (const block of blocks) {
      const validation = validateShellSyntax(block.content);
      if (validation.ok) {
        continue;
      }
      syntaxErrors.push({
        markdownPath,
        line: block.startLine,
        message: validation.message || 'shell syntax validation failed',
      });
    }
  }

  const exitCode = missingDocs.length > 0 || syntaxErrors.length > 0 ? 1 : 0;
  return {
    ...options,
    docsScanned,
    missingDocs,
    shellBlocksScanned,
    syntaxErrors,
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
  console.log(`Usage: node scripts/docs/check-runbook-command-blocks.mjs [options]

Options:
  --docs <file1,file2>   Comma separated markdown files to inspect
  --root <dir>           Repository root directory (default: current directory)
  --format <text|json>   Output format (default: text)
  -h, --help             Show this help
`);
}

function main(argv = process.argv) {
  const result = runRunbookCommandCheck(argv);
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
      shellBlocksScanned: result.shellBlocksScanned,
      syntaxErrors: result.syntaxErrors,
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
