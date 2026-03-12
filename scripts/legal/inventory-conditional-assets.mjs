#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { classifyArtifact } from '../maintenance/tracked-artifact-inventory.mjs';

export const CONDITIONAL_PREFIXES = ['artifacts/', 'fixtures/', 'test-cassettes/'];
export const NOTICE_BASENAMES = ['LICENSE', 'NOTICE', 'COPYING'];

function normalizePath(value) {
  return String(value || '').replace(/\\/g, '/').replace(/^\.\/+/, '');
}

function compareCodePointOrder(left, right) {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

function runGit(rootDir, args) {
  const result = spawnSync('git', args, {
    cwd: rootDir,
    encoding: 'utf8',
  });
  if (result.status !== 0) {
    const stderr = result.stderr?.trim() || 'git command failed';
    throw new Error(stderr);
  }
  return result.stdout;
}

export function listConditionalTrackedFiles(rootDir) {
  const output = runGit(rootDir, ['ls-files', '-z', '--', ...CONDITIONAL_PREFIXES]);
  return output
    .split('\0')
    .filter((entry) => entry !== '')
    .map(normalizePath)
    .sort(compareCodePointOrder);
}

export function classifyConditionalOrigin(filePath) {
  const normalized = normalizePath(filePath);
  if (normalized.startsWith('fixtures/')) {
    return 'test-fixture';
  }
  if (normalized.startsWith('test-cassettes/')) {
    return 'test-cassette';
  }
  if (!normalized.startsWith('artifacts/')) {
    return 'unclassified';
  }

  const artifactClass = classifyArtifact(normalized);
  switch (artifactClass) {
    case 'committed-contract':
      return 'committed-contract-artifact';
    case 'reference-snapshot':
      return 'tracked-reference-snapshot';
    case 'archive':
      return 'tracked-archive';
    case 'local-debug-archive':
      return 'local-debug-archive';
    default:
      return 'runtime-output-or-unclassified';
  }
}

function isNestedNoticeFile(filePath) {
  const normalized = normalizePath(filePath);
  if (!normalized.includes('/')) {
    return false;
  }
  const baseName = path.basename(normalized).toUpperCase();
  return NOTICE_BASENAMES.some((prefix) => baseName.startsWith(prefix));
}

function summarizeBy(items, selector) {
  return items.reduce((acc, item) => {
    const key = selector(item);
    acc[key] = (acc[key] || 0) + 1;
    return acc;
  }, {});
}

export function buildConditionalAssetAudit({
  trackedFiles,
  generatedAt = new Date().toISOString(),
}) {
  const items = trackedFiles.map((filePath) => {
    const normalized = normalizePath(filePath);
    const scope = CONDITIONAL_PREFIXES.find((prefix) => normalized.startsWith(prefix))?.replace(/\/$/, '') ?? 'other';
    return {
      path: normalized,
      scope,
      originClass: classifyConditionalOrigin(normalized),
      nestedNotice: isNestedNoticeFile(normalized),
    };
  });

  return {
    schemaVersion: 'conditional-asset-audit/v1',
    generatedAt,
    summary: {
      total: items.length,
      byScope: summarizeBy(items, (item) => item.scope),
      byOriginClass: summarizeBy(items, (item) => item.originClass),
      nestedNoticeFiles: items.filter((item) => item.nestedNotice).length,
    },
    nestedNoticeFiles: items.filter((item) => item.nestedNotice).map((item) => item.path),
    items,
  };
}

export function renderMarkdownReport(audit) {
  const lines = [
    '# Conditional Asset Provenance Audit',
    '',
    `- generatedAt: ${audit.generatedAt}`,
    `- total: ${audit.summary.total}`,
    '',
    '## By scope',
  ];

  for (const [scope, count] of Object.entries(audit.summary.byScope)) {
    lines.push(`- ${scope}: ${count}`);
  }

  lines.push('', '## By origin class');
  for (const [originClass, count] of Object.entries(audit.summary.byOriginClass)) {
    lines.push(`- ${originClass}: ${count}`);
  }

  lines.push('', '## Nested notice files');
  if (audit.nestedNoticeFiles.length === 0) {
    lines.push('- none');
  } else {
    for (const filePath of audit.nestedNoticeFiles) {
      lines.push(`- ${filePath}`);
    }
  }

  lines.push('', '## Items', '', '| Path | Scope | Origin class | Nested notice |', '| --- | --- | --- | --- |');
  for (const item of audit.items) {
    lines.push(`| \`${item.path}\` | ${item.scope} | ${item.originClass} | ${item.nestedNotice ? 'yes' : 'no'} |`);
  }
  return `${lines.join('\n')}\n`;
}

function parseArgs(argv) {
  const options = {
    root: process.cwd(),
    outputJson: null,
    outputMd: null,
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }
    const next = argv[index + 1];
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--root') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --root');
      }
      options.root = next;
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --output-json');
      }
      options.outputJson = next;
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --output-md');
      }
      options.outputMd = next;
      index += 1;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(`Conditional asset provenance audit

Usage:
  node scripts/legal/inventory-conditional-assets.mjs [options]

Options:
  --root <path>         Repository root (default: current working directory)
  --output-json <path>  Write JSON report
  --output-md <path>    Write Markdown report
  --help, -h            Show this help
`);
}

export function run(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }

  const rootDir = path.resolve(options.root);
  const audit = buildConditionalAssetAudit({
    trackedFiles: listConditionalTrackedFiles(rootDir),
  });

  if (options.outputJson) {
    const outputJsonPath = path.resolve(rootDir, options.outputJson);
    fs.mkdirSync(path.dirname(outputJsonPath), { recursive: true });
    fs.writeFileSync(outputJsonPath, `${JSON.stringify(audit, null, 2)}\n`);
  }

  if (options.outputMd) {
    const outputMdPath = path.resolve(rootDir, options.outputMd);
    fs.mkdirSync(path.dirname(outputMdPath), { recursive: true });
    fs.writeFileSync(outputMdPath, renderMarkdownReport(audit));
  }

  process.stdout.write(`${JSON.stringify(audit, null, 2)}\n`);
  return 0;
}

export function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  if (!argvPath) {
    return false;
  }
  return importMetaUrl === pathToFileURL(path.resolve(argvPath)).href;
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  try {
    process.exit(run(process.argv));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`[conditional-asset-audit] ${message}\n`);
    process.exit(1);
  }
}
