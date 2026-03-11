#!/usr/bin/env node

import { existsSync, readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const ROOT_DOCS = ['README.md', 'AGENTS.md', 'docs/README.md'];
const GOVERNED_EXTRA_DOCS = ['docs/reference/DOC-GOVERNANCE.md'];
const GOVERNED_PREFIX_DIRS = ['docs/agents', 'docs/ci', 'docs/development', 'docs/flows', 'docs/getting-started', 'docs/guides', 'docs/integrations', 'docs/maintenance', 'docs/operate', 'docs/product', 'docs/project', 'docs/quality', 'docs/reference', 'docs/strategy', 'docs/trace', 'docs/workflows'];
const DOC_ROLE_VALUES = new Set(['ssot', 'derived', 'narrative']);
const NARRATIVE_NORMATIVE_PATTERNS = [
  /\bmust\b/giu,
  /\brequired\b/giu,
  /禁止/gu,
  /必須/gu,
];

function parseArgs(argv = process.argv) {
  const options = {
    rootDir: process.cwd(),
    format: 'text',
    help: false,
    unknown: [],
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--root') {
      if (!next || next.startsWith('-')) {
        options.unknown.push(arg);
      } else {
        options.rootDir = path.resolve(next);
        index += 1;
      }
      continue;
    }
    if (arg.startsWith('--root=')) {
      options.rootDir = path.resolve(arg.slice('--root='.length));
      continue;
    }
    if (arg === '--format') {
      if (next === 'text' || next === 'json') {
        options.format = next;
        index += 1;
      } else {
        options.unknown.push(arg);
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
    options.unknown.push(arg);
  }

  return options;
}

function printHelp() {
  process.stdout.write(
    'Doc governance checker\n\n'
      + 'Usage:\n'
      + '  node scripts/docs/check-doc-governance.mjs [--root <path>] [--format text|json]\n\n'
      + 'Checks docRole/canonicalSource/lastVerified front matter for governed docs.\n',
  );
}

function collectGovernedDocs(rootDir) {
  const docs = new Set([...ROOT_DOCS, ...GOVERNED_EXTRA_DOCS]);
  for (const dir of GOVERNED_PREFIX_DIRS) {
    const absoluteDir = path.join(rootDir, dir);
    if (!existsSync(absoluteDir)) {
      continue;
    }
    const entries = readdirSync(absoluteDir, { withFileTypes: true })
      .filter((entry) => entry.isFile() && entry.name.endsWith('.md'))
      .map((entry) => `${dir}/${entry.name}`)
      .sort();
    for (const entry of entries) {
      docs.add(entry);
    }
  }
  return [...docs];
}

function extractFrontMatter(raw) {
  const source = String(raw ?? '');
  const match = /^---\r?\n([\s\S]*?)\r?\n---(?:\r?\n|$)/u.exec(source);
  if (!match) {
    return { data: null, body: source, parseError: null };
  }
  const yamlBlock = match[1];
  const body = source.slice(match[0].length);
  try {
    const data = parseFrontMatterMapping(yamlBlock);
    return { data, body, parseError: null };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return { data: null, body, parseError: message };
  }
}

function normalizeScalar(value) {
  const trimmed = String(value ?? '').trim();
  if (
    (trimmed.startsWith('"') && trimmed.endsWith('"'))
    || (trimmed.startsWith('\'') && trimmed.endsWith('\''))
  ) {
    return trimmed.slice(1, -1);
  }
  return trimmed;
}

function parseFrontMatterMapping(yamlBlock) {
  const parsed = {};
  const lines = String(yamlBlock).split(/\r?\n/u);
  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    if (!line.trim()) {
      continue;
    }
    const topLevelMatch = /^([A-Za-z][A-Za-z0-9]*):(?:\s*(.*))?$/u.exec(line);
    if (!topLevelMatch) {
      throw new Error(`unsupported front matter syntax at line ${index + 1}`);
    }
    const [, key, inlineValue = ''] = topLevelMatch;
    if (inlineValue.startsWith('[') || inlineValue.startsWith('{')) {
      throw new Error(`inline collections are not supported at line ${index + 1}`);
    }
    if (inlineValue.trim()) {
      parsed[key] = normalizeScalar(inlineValue);
      continue;
    }

    const sequence = [];
    let nextIndex = index + 1;
    while (nextIndex < lines.length) {
      const nextLine = lines[nextIndex];
      if (!nextLine.trim()) {
        nextIndex += 1;
        continue;
      }
      const sequenceMatch = /^\s*-\s+(.+)$/u.exec(nextLine);
      if (!sequenceMatch) {
        break;
      }
      sequence.push(normalizeScalar(sequenceMatch[1]));
      nextIndex += 1;
    }
    if (sequence.length > 0) {
      parsed[key] = sequence;
      index = nextIndex - 1;
      continue;
    }
    parsed[key] = '';
  }
  return parsed;
}

function normalizeCanonicalSources(value) {
  if (typeof value === 'string' && value.trim()) {
    return [value.trim()];
  }
  if (Array.isArray(value)) {
    return value
      .map((entry) => (typeof entry === 'string' ? entry.trim() : ''))
      .filter(Boolean);
  }
  return [];
}

function hasValidDate(value) {
  return typeof value === 'string' && /^\d{4}-\d{2}-\d{2}$/.test(value);
}

function stripCodeBlocks(body) {
  return body
    .replace(/```[\s\S]*?```/g, ' ')
    .replace(/`[^`\n]+`/g, ' ');
}

function checkNarrativeWarnings(markdownPath, body) {
  const warnings = [];
  const plainBody = stripCodeBlocks(body);
  const lines = plainBody.split(/\r?\n/u);
  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    for (const pattern of NARRATIVE_NORMATIVE_PATTERNS) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        warnings.push({
          markdownPath,
          line: index + 1,
          message: `narrative doc contains normative wording: ${line.trim()}`,
        });
        break;
      }
    }
  }
  return warnings;
}

function validateDoc(rootDir, markdownPath) {
  const absolutePath = path.join(rootDir, markdownPath);
  if (!existsSync(absolutePath)) {
    return {
      failures: [{ markdownPath, message: 'governed markdown file not found' }],
      warnings: [],
    };
  }
  const raw = readFileSync(absolutePath, 'utf8');
  const { data, body, parseError } = extractFrontMatter(raw);
  const failures = [];
  const warnings = [];

  if (parseError) {
    failures.push({ markdownPath, message: `invalid YAML front matter: ${parseError}` });
    return { failures, warnings };
  }

  if (!data || typeof data !== 'object' || Array.isArray(data)) {
    failures.push({ markdownPath, message: 'missing or invalid YAML front matter' });
    return { failures, warnings };
  }

  const role = data.docRole;
  if (!DOC_ROLE_VALUES.has(role)) {
    failures.push({ markdownPath, message: 'docRole must be one of: ssot, derived, narrative' });
  }

  if (!hasValidDate(data.lastVerified)) {
    failures.push({ markdownPath, message: 'lastVerified must be YYYY-MM-DD' });
  }

  const canonicalSources = normalizeCanonicalSources(data.canonicalSource);
  if (role === 'derived' && canonicalSources.length === 0) {
    failures.push({ markdownPath, message: 'derived docs must declare canonicalSource' });
  }
  for (const canonicalSource of canonicalSources) {
    const absoluteCanonicalSource = path.join(rootDir, canonicalSource);
    if (!existsSync(absoluteCanonicalSource)) {
      failures.push({ markdownPath, message: `canonicalSource not found: ${canonicalSource}` });
    }
  }

  if (role === 'ssot') {
    if (typeof data.owner !== 'string' || data.owner.trim().length === 0) {
      failures.push({ markdownPath, message: 'ssot docs must declare owner' });
    }
    if (typeof data.verificationCommand !== 'string' || data.verificationCommand.trim().length === 0) {
      failures.push({ markdownPath, message: 'ssot docs must declare verificationCommand' });
    }
  }

  if (role === 'narrative') {
    warnings.push(...checkNarrativeWarnings(markdownPath, body));
  }

  return { failures, warnings };
}

function printText(result) {
  process.stdout.write('Doc governance check\n');
  process.stdout.write(`- root: ${result.rootDir}\n`);
  process.stdout.write(`- docs scanned: ${result.docsScanned}\n`);
  process.stdout.write(`- failures: ${result.failures.length}\n`);
  process.stdout.write(`- warnings: ${result.warnings.length}\n`);
  if (result.failures.length > 0) {
    for (const failure of result.failures) {
      process.stderr.write(`[doc-governance] ${failure.markdownPath}: ${failure.message}\n`);
    }
  }
  if (result.warnings.length > 0) {
    for (const warning of result.warnings) {
      process.stdout.write(`[doc-governance:warn] ${warning.markdownPath}:${warning.line} ${warning.message}\n`);
    }
  }
}

export function main(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }
  if (options.unknown.length > 0) {
    process.stderr.write(`[doc-governance] unknown options: ${options.unknown.join(', ')}\n`);
    return 1;
  }

  const governedDocs = collectGovernedDocs(options.rootDir);
  const failures = [];
  const warnings = [];
  for (const markdownPath of governedDocs) {
    const result = validateDoc(options.rootDir, markdownPath);
    failures.push(...result.failures);
    warnings.push(...result.warnings);
  }

  const summary = {
    rootDir: options.rootDir,
    docsScanned: governedDocs.length,
    failures,
    warnings,
  };

  if (options.format === 'json') {
    process.stdout.write(`${JSON.stringify(summary, null, 2)}\n`);
  } else {
    printText(summary);
  }

  return failures.length === 0 ? 0 : 1;
}

if (process.argv[1] && path.resolve(process.argv[1]) === __filename) {
  process.exit(main(process.argv));
}
