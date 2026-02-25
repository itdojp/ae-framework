#!/usr/bin/env node

import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const DEFAULT_INDEX_FILES = [
  'docs/README.md',
  'docs/ci-policy.md',
];

export const REQUIRED_LINKS = {
  'docs/README.md': [
    'ci-policy.md',
    'ci/docs-doctest-policy.md',
    'ci/ci-operations-handbook.md',
    'ci/ci-troubleshooting-guide.md',
    'ci/pr-automation.md',
    'ci/workflow-role-matrix.md',
    'ci/OPT-IN-CONTROLS.md',
  ],
  'docs/ci-policy.md': [
    'docs/ci/docs-doctest-policy.md',
    'docs/ci/ci-operations-handbook.md',
    'docs/ci/ci-troubleshooting-guide.md',
    'docs/ci/pr-automation.md',
    'docs/ci/workflow-role-matrix.md',
    'docs/ci/OPT-IN-CONTROLS.md',
  ],
};

export const SECTION_RULES = [
  {
    file: 'docs/ci-policy.md',
    heading: '### 参考ドキュメント',
    requiredLinks: [
      'docs/ci/docs-doctest-policy.md',
      'docs/ci/ci-operations-handbook.md',
      'docs/ci/ci-troubleshooting-guide.md',
      'docs/ci/pr-automation.md',
    ],
  },
  {
    file: 'docs/ci-policy.md',
    heading: '## 6. 参照',
    requiredLinks: [
      'docs/ci/docs-doctest-policy.md',
      'docs/ci/ci-operations-handbook.md',
      'docs/ci/ci-troubleshooting-guide.md',
      'docs/ci/pr-automation.md',
    ],
  },
];

const MARKDOWN_LINK_REGEX = /\[[^\]]*]\(([^)\s]+)\)/g;
const INLINE_CODE_REGEX = /`([^`\n]+)`/g;
const BARE_DOC_PATH_REGEX = /\b(?:docs\/[A-Za-z0-9._/-]+\.md|ci\/[A-Za-z0-9._/-]+\.md)\b/g;

function sanitizeReference(reference) {
  if (!reference) {
    return '';
  }
  return reference.trim().replace(/[),.;:]+$/g, '');
}

function stripFragmentAndQuery(reference) {
  const hashIndex = reference.indexOf('#');
  const queryIndex = reference.indexOf('?');
  let cutoff = reference.length;
  if (hashIndex >= 0) {
    cutoff = Math.min(cutoff, hashIndex);
  }
  if (queryIndex >= 0) {
    cutoff = Math.min(cutoff, queryIndex);
  }
  return reference.slice(0, cutoff);
}

function isExternalReference(reference) {
  return /^(?:https?:\/\/|mailto:|tel:)/i.test(reference);
}

function isMarkdownDocReference(reference) {
  if (!reference) {
    return false;
  }
  if (reference.startsWith('#') || isExternalReference(reference)) {
    return false;
  }
  if (reference.includes('*') || reference.includes('${')) {
    return false;
  }
  return /\.md$/i.test(stripFragmentAndQuery(reference));
}

export function parseArgs(argv = process.argv) {
  const options = {
    rootDir: process.cwd(),
    format: 'text',
    files: [...DEFAULT_INDEX_FILES],
    unknown: [],
    help: false,
  };

  const files = [];
  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
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
    if (arg.startsWith('--files=')) {
      const value = arg.slice('--files='.length);
      if (value.length === 0) {
        options.unknown.push(arg);
      } else {
        files.push(...value.split(',').map((entry) => entry.trim()).filter(Boolean));
      }
      continue;
    }
    if (arg === '--files') {
      const next = argv[index + 1];
      if (!next || next.startsWith('-')) {
        options.unknown.push(arg);
      } else {
        files.push(...next.split(',').map((entry) => entry.trim()).filter(Boolean));
        index += 1;
      }
      continue;
    }
    if (arg === '--') {
      continue;
    }
    options.unknown.push(arg);
  }

  if (files.length > 0) {
    options.files = files;
  }
  return options;
}

function collectReferencesRaw(rawContent) {
  const references = [];

  for (const match of rawContent.matchAll(MARKDOWN_LINK_REGEX)) {
    const reference = sanitizeReference(match[1]);
    if (isMarkdownDocReference(reference)) {
      references.push(stripFragmentAndQuery(reference));
    }
  }

  for (const match of rawContent.matchAll(INLINE_CODE_REGEX)) {
    const reference = sanitizeReference(match[1]);
    if (isMarkdownDocReference(reference)) {
      references.push(stripFragmentAndQuery(reference));
    }
  }

  for (const match of rawContent.matchAll(BARE_DOC_PATH_REGEX)) {
    references.push(stripFragmentAndQuery(match[0]));
  }

  return references;
}

function collectReferences(rawContent) {
  return [...new Set(collectReferencesRaw(rawContent))];
}

function resolveReferencePath(rootDir, sourceFile, reference) {
  if (reference.startsWith('docs/')) {
    return path.resolve(rootDir, reference);
  }
  const sourceDir = path.dirname(path.resolve(rootDir, sourceFile));
  return path.resolve(sourceDir, reference);
}

function extractSection(rawContent, heading) {
  const lines = rawContent.split('\n');
  const startIndex = lines.findIndex((line) => line.trim() === heading);
  if (startIndex < 0) {
    return null;
  }

  const sectionLevelMatch = heading.match(/^(#+)\s+/);
  const sectionLevel = sectionLevelMatch ? sectionLevelMatch[1].length : 6;
  const sectionLines = [];
  for (let index = startIndex + 1; index < lines.length; index += 1) {
    const line = lines[index];
    const headingMatch = line.match(/^(#+)\s+/);
    if (headingMatch && headingMatch[1].length <= sectionLevel) {
      break;
    }
    sectionLines.push(line);
  }
  return sectionLines.join('\n');
}

function collectSectionReferences(section) {
  const references = [];
  const lineRegex = /(?:docs\/[A-Za-z0-9._/-]+\.md|ci\/[A-Za-z0-9._/-]+\.md|[A-Za-z0-9._-]+\.md)/;
  for (const line of section.split('\n')) {
    const trimmed = line.trim();
    if (!trimmed.startsWith('-')) {
      continue;
    }
    const match = trimmed.match(lineRegex);
    if (!match) {
      continue;
    }
    const reference = stripFragmentAndQuery(sanitizeReference(match[0]));
    references.push(reference);
  }
  return references;
}

function checkSectionRules(rawContent, sourceFile, rootDir, findings) {
  for (const rule of SECTION_RULES) {
    if (rule.file !== sourceFile) {
      continue;
    }
    const section = extractSection(rawContent, rule.heading);
    if (section == null) {
      findings.push({
        code: 'missing_section',
        sourceFile,
        message: `${sourceFile} is missing section: ${rule.heading}`,
      });
      continue;
    }

    const references = collectSectionReferences(section)
      .map((reference) => ({
        reference,
        resolvedPath: path.relative(rootDir, resolveReferencePath(rootDir, sourceFile, reference)),
      }))
      .sort((a, b) => a.resolvedPath.localeCompare(b.resolvedPath));

    const seen = new Set();
    for (const item of references) {
      if (!seen.has(item.resolvedPath)) {
        seen.add(item.resolvedPath);
        continue;
      }
      findings.push({
        code: 'duplicate_reference',
        sourceFile,
        message: `${sourceFile} section "${rule.heading}" has duplicate reference: ${item.reference}`,
      });
    }

    for (const requiredLink of rule.requiredLinks) {
      if (!section.includes(requiredLink)) {
        findings.push({
          code: 'missing_section_link',
          sourceFile,
          message: `${sourceFile} section "${rule.heading}" must include: ${requiredLink}`,
        });
      }
    }
  }
}

export function runCiDocIndexConsistencyCheck(argv = process.argv) {
  const options = parseArgs(argv);
  const findings = [];
  const scannedFiles = [];

  if (options.unknown.length > 0) {
    return {
      exitCode: 1,
      options,
      scannedFiles,
      findings: options.unknown.map((argument) => ({
        code: 'unknown_option',
        message: `Unknown option: ${argument}`,
      })),
    };
  }

  for (const sourceFile of options.files) {
    const sourcePath = path.resolve(options.rootDir, sourceFile);
    scannedFiles.push(sourceFile);

    if (!existsSync(sourcePath)) {
      findings.push({
        code: 'missing_source',
        sourceFile,
        message: `${sourceFile} does not exist`,
      });
      continue;
    }

    const rawContent = readFileSync(sourcePath, 'utf8');

    const requiredLinks = REQUIRED_LINKS[sourceFile] ?? [];
    for (const requiredLink of requiredLinks) {
      if (!rawContent.includes(requiredLink)) {
        findings.push({
          code: 'missing_required_link',
          sourceFile,
          message: `${sourceFile} must include required link: ${requiredLink}`,
        });
      }

      const resolvedRequiredPath = resolveReferencePath(options.rootDir, sourceFile, requiredLink);
      if (!existsSync(resolvedRequiredPath)) {
        findings.push({
          code: 'missing_required_target',
          sourceFile,
          message: `Required target does not exist: ${requiredLink} -> ${path.relative(options.rootDir, resolvedRequiredPath)}`,
        });
      }
    }

    for (const reference of collectReferences(rawContent)) {
      const resolvedPath = resolveReferencePath(options.rootDir, sourceFile, reference);
      if (existsSync(resolvedPath)) {
        continue;
      }
      findings.push({
        code: 'missing_reference_target',
        sourceFile,
        message: `${sourceFile} references missing target: ${reference} -> ${path.relative(options.rootDir, resolvedPath)}`,
      });
    }

    checkSectionRules(rawContent, sourceFile, options.rootDir, findings);
  }

  return {
    exitCode: findings.length > 0 ? 1 : 0,
    options,
    scannedFiles,
    findings,
  };
}

function renderText(result) {
  const lines = [];
  lines.push('CI docs index consistency check');
  lines.push(`- files scanned: ${result.scannedFiles.length}`);
  lines.push(`- findings: ${result.findings.length}`);
  if (result.findings.length > 0) {
    lines.push('');
    for (const finding of result.findings) {
      lines.push(`- [${finding.code}] ${finding.message}`);
    }
  }
  return lines.join('\n');
}

function printUsage() {
  console.log(`Usage: node scripts/docs/check-ci-doc-index-consistency.mjs [options]

Options:
  --root <path>              Repository root (default: cwd)
  --format <text|json>       Output format (default: text)
  --files <a,b,c>            Comma-separated markdown files to check
  -h, --help                 Show this help
`);
}

export function main(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printUsage();
    return {
      exitCode: 0,
      options,
      scannedFiles: [],
      findings: [],
    };
  }

  const result = runCiDocIndexConsistencyCheck(argv);
  if (options.format === 'json') {
    console.log(JSON.stringify(result, null, 2));
  } else {
    console.log(renderText(result));
  }
  return result;
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
  const result = main(process.argv);
  process.exit(result.exitCode);
}
