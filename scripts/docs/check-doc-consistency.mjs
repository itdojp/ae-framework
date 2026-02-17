#!/usr/bin/env node

import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const DEFAULT_DOC_FILES = [
  'README.md',
  'docs/README.md',
  'docs/getting-started/QUICK-START-GUIDE.md',
  'docs/product/USER-MANUAL.md',
  'docs/integrations/QUICK-START-CODEX.md',
];

const PNPM_RUN_REGEX = /\bpnpm\s+(?:-s\s+)?run\s+([A-Za-z0-9:_-]+)\b/g;
const MARKDOWN_LINK_REGEX = /\[[^\]]*]\(([^)\s]+)\)/g;
const INLINE_CODE_REGEX = /`([^`\n]+)`/g;
const ROOT_RELATIVE_PREFIXES = [
  '.github/',
  'api/',
  'apps/',
  'artifacts/',
  'config/',
  'configs/',
  'contracts/',
  'docs/',
  'examples/',
  'fixtures/',
  'packages/',
  'plans/',
  'samples/',
  'schema/',
  'scripts/',
  'spec/',
  'src/',
];

function sanitizeReference(rawReference) {
  if (!rawReference) {
    return '';
  }
  let reference = rawReference.trim();
  if (reference.startsWith('<') && reference.endsWith('>')) {
    reference = reference.slice(1, -1);
  }
  reference = reference.replace(/[),.;:]+$/, '');
  return reference;
}

function stripFragmentAndQuery(reference) {
  const questionIndex = reference.indexOf('?');
  const hashIndex = reference.indexOf('#');
  let cutoff = reference.length;
  if (questionIndex >= 0) {
    cutoff = Math.min(cutoff, questionIndex);
  }
  if (hashIndex >= 0) {
    cutoff = Math.min(cutoff, hashIndex);
  }
  return reference.slice(0, cutoff);
}

function isExternalReference(reference) {
  return /^(?:https?:\/\/|mailto:|tel:|data:|javascript:)/i.test(reference);
}

function isPathLikeReference(reference) {
  if (!reference) {
    return false;
  }
  if (reference.startsWith('#') || isExternalReference(reference)) {
    return false;
  }
  if (reference.includes('*') || reference.includes('${')) {
    return false;
  }
  if (reference.includes('<') || reference.includes('>')) {
    return false;
  }
  if (reference.includes(' ')) {
    return false;
  }
  if (reference.includes('\\') || reference.includes('/')) {
    return true;
  }
  return /\.[A-Za-z0-9_-]+$/u.test(reference);
}

function isExplicitRelativeReference(reference) {
  return reference.startsWith('./') || reference.startsWith('../');
}

function isRootRelativeReference(reference) {
  return ROOT_RELATIVE_PREFIXES.some((prefix) => reference === prefix || reference.startsWith(prefix));
}

export function parseArgs(argv = process.argv) {
  const options = {
    rootDir: process.cwd(),
    format: 'text',
    docs: [...DEFAULT_DOC_FILES],
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
    if (arg.startsWith('--format=')) {
      const value = arg.slice('--format='.length);
      if (value === 'text' || value === 'json') {
        options.format = value;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    if (arg === '--format') {
      const next = argv[index + 1];
      if (next === 'text' || next === 'json') {
        options.format = next;
        index += 1;
      } else {
        options.unknown.push(arg);
      }
      continue;
    }
    if (arg.startsWith('--docs=')) {
      const value = arg.slice('--docs='.length);
      if (value.length === 0) {
        options.unknown.push(arg);
      } else {
        for (const entry of value.split(',').map((item) => item.trim()).filter(Boolean)) {
          docs.push(entry);
        }
      }
      continue;
    }
    if (arg === '--docs') {
      const next = argv[index + 1];
      if (!next || next.startsWith('-')) {
        options.unknown.push(arg);
      } else {
        for (const entry of next.split(',').map((item) => item.trim()).filter(Boolean)) {
          docs.push(entry);
        }
        index += 1;
      }
      continue;
    }
    options.unknown.push(arg);
  }

  if (docs.length > 0) {
    options.docs = docs;
  }
  return options;
}

function loadPackageScripts(rootDir) {
  const packageJsonPath = path.join(rootDir, 'package.json');
  try {
    const packageJson = JSON.parse(readFileSync(packageJsonPath, 'utf8'));
    const scripts = packageJson.scripts && typeof packageJson.scripts === 'object'
      ? Object.keys(packageJson.scripts)
      : [];
    return {
      scripts: new Set(scripts),
      error: null,
    };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return {
      scripts: new Set(),
      error: {
        code: 'package_json_read_error',
        message: `Failed to load package.json: ${message}`,
      },
    };
  }
}

function resolveReferencePath(rootDir, markdownPath, reference) {
  if (path.isAbsolute(reference)) {
    return null;
  }
  const markdownDir = path.dirname(path.resolve(rootDir, markdownPath));
  if (isExplicitRelativeReference(reference)) {
    return path.resolve(markdownDir, reference);
  }
  if (isRootRelativeReference(reference)) {
    return path.resolve(rootDir, reference);
  }
  return path.resolve(markdownDir, reference);
}

function collectMissingScripts(markdownPath, lines, scriptNames) {
  const missingScripts = [];
  for (let lineNumber = 0; lineNumber < lines.length; lineNumber += 1) {
    const line = lines[lineNumber];
    PNPM_RUN_REGEX.lastIndex = 0;
    for (const match of line.matchAll(PNPM_RUN_REGEX)) {
      const scriptName = match[1];
      if (!scriptName || scriptNames.has(scriptName)) {
        continue;
      }
      missingScripts.push({
        markdownPath,
        line: lineNumber + 1,
        scriptName,
        command: match[0],
      });
    }
  }
  return missingScripts;
}

function shouldCheckInlineReference(reference) {
  if (!reference) {
    return false;
  }
  if (reference.startsWith('docs/')) {
    return true;
  }
  return /\.md$/i.test(reference);
}

function collectMarkdownReferences(line, regex, sourceType) {
  const references = [];
  regex.lastIndex = 0;
  for (const match of line.matchAll(regex)) {
    const candidate = sanitizeReference(match[1]);
    if (!isPathLikeReference(candidate)) {
      continue;
    }
    if (sourceType === 'inline' && !shouldCheckInlineReference(candidate)) {
      continue;
    }
    references.push(candidate);
  }
  return references;
}

function collectMissingPaths(rootDir, markdownPath, lines) {
  const missingPaths = [];
  for (let lineNumber = 0; lineNumber < lines.length; lineNumber += 1) {
    const line = lines[lineNumber];
    const references = [
      ...collectMarkdownReferences(line, MARKDOWN_LINK_REGEX, 'link'),
      ...collectMarkdownReferences(line, INLINE_CODE_REGEX, 'inline'),
    ];
    const uniqueReferences = [...new Set(references)];
    for (const reference of uniqueReferences) {
      const normalizedReference = stripFragmentAndQuery(reference);
      if (!normalizedReference) {
        continue;
      }
      const resolvedPath = resolveReferencePath(rootDir, markdownPath, normalizedReference);
      if (!resolvedPath) {
        continue;
      }
      if (existsSync(resolvedPath)) {
        continue;
      }
      missingPaths.push({
        markdownPath,
        line: lineNumber + 1,
        reference,
        resolvedPath: path.relative(rootDir, resolvedPath),
      });
    }
  }
  return missingPaths;
}

function renderText(result) {
  const lines = [];
  lines.push('Doc consistency check');
  lines.push(`- docs scanned: ${result.docsScanned.length}`);
  lines.push(`- missing docs: ${result.missingDocs.length}`);
  lines.push(`- package errors: ${result.packageErrors.length}`);
  lines.push(`- missing scripts: ${result.missingScripts.length}`);
  lines.push(`- missing paths: ${result.missingPaths.length}`);

  if (result.packageErrors.length > 0) {
    lines.push('', 'Package errors:');
    for (const finding of result.packageErrors) {
      lines.push(`- ${finding.code}: ${finding.message}`);
    }
  }

  if (result.missingDocs.length > 0) {
    lines.push('', 'Missing docs:');
    for (const finding of result.missingDocs) {
      lines.push(`- ${finding.markdownPath}: ${finding.message}`);
    }
  }

  if (result.missingScripts.length > 0) {
    lines.push('', 'Missing pnpm scripts:');
    for (const finding of result.missingScripts) {
      lines.push(`- ${finding.markdownPath}:${finding.line} -> ${finding.command} (script: ${finding.scriptName})`);
    }
  }

  if (result.missingPaths.length > 0) {
    lines.push('', 'Missing file paths:');
    for (const finding of result.missingPaths) {
      lines.push(`- ${finding.markdownPath}:${finding.line} -> ${finding.reference} (resolved: ${finding.resolvedPath})`);
    }
  }

  return `${lines.join('\n')}\n`;
}

export function runDocConsistencyCheck(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    return {
      ...options,
      docsScanned: [],
      missingDocs: [],
      packageErrors: [],
      missingScripts: [],
      missingPaths: [],
      exitCode: 0,
      help: true,
    };
  }
  if (options.unknown.length > 0) {
    return {
      ...options,
      docsScanned: [],
      missingDocs: [],
      packageErrors: [],
      missingScripts: [],
      missingPaths: [],
      exitCode: 2,
      help: false,
    };
  }

  const packageErrors = [];
  const packageScriptsResult = loadPackageScripts(options.rootDir);
  const scriptNames = packageScriptsResult.scripts;
  if (packageScriptsResult.error) {
    packageErrors.push(packageScriptsResult.error);
  }
  const missingDocs = [];
  const missingScripts = [];
  const missingPaths = [];
  const docsScanned = [];

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
    const lines = content.split(/\r?\n/u);
    missingScripts.push(...collectMissingScripts(markdownPath, lines, scriptNames));
    missingPaths.push(...collectMissingPaths(options.rootDir, markdownPath, lines));
  }

  const hasFailures = packageErrors.length > 0 || missingDocs.length > 0 || missingScripts.length > 0 || missingPaths.length > 0;
  return {
    ...options,
    docsScanned,
    missingDocs,
    packageErrors,
    missingScripts,
    missingPaths,
    exitCode: hasFailures ? 1 : 0,
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
  console.log(`Usage: node scripts/docs/check-doc-consistency.mjs [options]

Options:
  --docs <file1,file2>   Comma separated markdown files to inspect
  --root <dir>           Repository root directory (default: current directory)
  --format <text|json>   Output format (default: text)
  -h, --help             Show this help
`);
}

function main(argv = process.argv) {
  const result = runDocConsistencyCheck(argv);
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
    console.log(JSON.stringify({
      docsScanned: result.docsScanned,
      missingDocs: result.missingDocs,
      packageErrors: result.packageErrors,
      missingScripts: result.missingScripts,
      missingPaths: result.missingPaths,
      exitCode: result.exitCode,
    }, null, 2));
  } else {
    process.stdout.write(renderText(result));
  }
  return result.exitCode;
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  process.exitCode = main(process.argv);
}
