#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { resolveGeneratedAt, resolveGitHeadSha } from './inventory-license-scope.mjs';
import { CONDITIONAL_PREFIXES } from './inventory-conditional-assets.mjs';

export const VENDOR_LIKE_SEGMENTS = [
  'vendor',
  'vendored',
  'third_party',
  'third-party',
  'upstream',
  'external',
];
export const NESTED_NOTICE_PATTERN = /^(LICENSE|NOTICE|COPYING)([._-].+|\.[A-Za-z0-9]+)?$/;
export const EXCLUDED_PREFIXES = ['docs/', 'tests/', ...CONDITIONAL_PREFIXES];

function normalizePath(value) {
  return String(value).replace(/\\/g, '/').replace(/^\.\/+/, '');
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
    throw new Error(result.stderr?.trim() || 'git command failed');
  }
  return result;
}

function runGitAllowNoMatch(rootDir, args) {
  const result = spawnSync('git', args, {
    cwd: rootDir,
    encoding: 'utf8',
  });
  if (result.status === 0) {
    return result;
  }
  const stdout = String(result.stdout || '').trim();
  const stderr = String(result.stderr || '').trim();
  if (result.status === 1 && stdout === '' && stderr === '') {
    return result;
  }
  throw new Error(stderr || 'git command failed');
}

export function listTrackedFiles(rootDir) {
  const result = runGit(rootDir, ['ls-files', '-z']);
  return result.stdout
    .split('\0')
    .filter((entry) => entry !== '')
    .map(normalizePath)
    .sort(compareCodePointOrder);
}

export function isNestedNoticeCandidate(filePath) {
  const normalized = normalizePath(filePath);
  if (!normalized.includes('/')) {
    return false;
  }
  if (EXCLUDED_PREFIXES.some((prefix) => normalized.startsWith(prefix))) {
    return false;
  }
  const baseName = path.basename(normalized);
  return NESTED_NOTICE_PATTERN.test(baseName);
}

export function collectVendoredPathCandidates(trackedFiles) {
  const byPath = new Map();
  for (const filePath of trackedFiles) {
    const normalized = normalizePath(filePath);
    const segments = normalized.split('/');
    for (let index = 0; index < segments.length - 1; index += 1) {
      const segment = segments[index];
      if (!VENDOR_LIKE_SEGMENTS.includes(segment)) {
        continue;
      }
      const candidatePath = segments.slice(0, index + 1).join('/');
      if (!byPath.has(candidatePath)) {
        byPath.set(candidatePath, {
          path: candidatePath,
          segment,
          sampleFile: normalized,
        });
      }
      break;
    }
  }
  return Array.from(byPath.values()).sort((left, right) => compareCodePointOrder(left.path, right.path));
}

export function listSubmodules(rootDir) {
  const gitmodulesPath = path.join(rootDir, '.gitmodules');
  if (!fs.existsSync(gitmodulesPath)) {
    return [];
  }

  const pathResult = runGitAllowNoMatch(
    rootDir,
    ['config', '-f', '.gitmodules', '--get-regexp', '^submodule\..*\.path$'],
  );
  const urlResult = runGitAllowNoMatch(
    rootDir,
    ['config', '-f', '.gitmodules', '--get-regexp', '^submodule\..*\.url$'],
  );

  const urls = new Map();
  for (const line of String(urlResult.stdout || '').split(/\r?\n/).filter(Boolean)) {
    const [key, ...rest] = line.split(' ');
    const value = rest.join(' ').trim();
    const match = key.match(/^submodule\.(.+)\.url$/);
    if (match) {
      urls.set(match[1], value || null);
    }
  }

  const entries = [];
  for (const line of String(pathResult.stdout || '').split(/\r?\n/).filter(Boolean)) {
    const [key, ...rest] = line.split(' ');
    const value = rest.join(' ').trim();
    const match = key.match(/^submodule\.(.+)\.path$/);
    if (match) {
      entries.push({
        path: normalizePath(value),
        url: urls.get(match[1]) ?? null,
      });
    }
  }

  return entries.sort((left, right) => compareCodePointOrder(left.path, right.path));
}

export function buildThirdPartyNoticeCandidateAudit({
  trackedFiles,
  submodules,
  gitHeadSha,
  generatedAt = new Date().toISOString(),
}) {
  const nestedNoticeFiles = trackedFiles.filter(isNestedNoticeCandidate);
  const vendoredPathCandidates = collectVendoredPathCandidates(trackedFiles);
  const reasons = [];

  if (nestedNoticeFiles.length > 0) {
    reasons.push('nested-legal-files-present');
  }
  if (vendoredPathCandidates.length > 0) {
    reasons.push('vendored-path-candidates-present');
  }
  if (submodules.length > 0) {
    reasons.push('submodules-present');
  }

  return {
    schemaVersion: 'third-party-notice-candidate-audit/v1',
    generatedAt,
    gitHeadSha: gitHeadSha ?? null,
    inputs: {
      trackedFilesScanned: trackedFiles.length,
      vendorLikeSegments: [...VENDOR_LIKE_SEGMENTS],
      nestedNoticePattern: NESTED_NOTICE_PATTERN.source,
    },
    summary: {
      nestedNoticeFileCount: nestedNoticeFiles.length,
      vendoredPathCount: vendoredPathCandidates.length,
      submoduleCount: submodules.length,
      status: reasons.length === 0 ? 'no-candidates' : 'review-required',
    },
    evidence: {
      nestedNoticeFiles,
      vendoredPathCandidates,
      submodules,
    },
    review: {
      requiresIndividualNoticeReview: reasons.length > 0,
      reasons,
    },
  };
}

const escapeHtml = (value) =>
  String(value ?? '')
    .replace(/&/g, '&amp;')
    .replace(/\\/g, '&#92;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');

const codeCell = (value) => `<code>${escapeHtml(value).replace(/\r?\n/g, '<br>')}</code>`;

export function renderMarkdownReport(audit) {
  const lines = [
    '# Third-Party Notice Candidate Audit',
    '',
    `- generatedAt: ${audit.generatedAt}`,
    `- gitHeadSha: ${audit.gitHeadSha ?? 'missing'}`,
    `- tracked files scanned: ${audit.inputs.trackedFilesScanned}`,
    `- status: ${audit.summary.status}`,
    '',
    '## Summary',
    `- nested notice files: ${audit.summary.nestedNoticeFileCount}`,
    `- vendored path candidates: ${audit.summary.vendoredPathCount}`,
    `- submodules: ${audit.summary.submoduleCount}`,
    '',
    '## Review reasons',
  ];

  if (audit.review.reasons.length === 0) {
    lines.push('- none');
  } else {
    for (const reason of audit.review.reasons) {
      lines.push(`- ${reason}`);
    }
  }

  lines.push('', '## Nested legal files');
  if (audit.evidence.nestedNoticeFiles.length === 0) {
    lines.push('- none');
  } else {
    lines.push('| Path |', '| --- |');
    for (const filePath of audit.evidence.nestedNoticeFiles) {
      lines.push(`| ${codeCell(filePath)} |`);
    }
  }

  lines.push('', '## Vendored path candidates');
  if (audit.evidence.vendoredPathCandidates.length === 0) {
    lines.push('- none');
  } else {
    lines.push('| Candidate path | Segment | Sample file |', '| --- | --- | --- |');
    for (const entry of audit.evidence.vendoredPathCandidates) {
      lines.push(
        `| ${codeCell(entry.path)} | ${codeCell(entry.segment)} | ${codeCell(entry.sampleFile)} |`,
      );
    }
  }

  lines.push('', '## Submodules');
  if (audit.evidence.submodules.length === 0) {
    lines.push('- none');
  } else {
    lines.push('| Path | URL |', '| --- | --- |');
    for (const entry of audit.evidence.submodules) {
      lines.push(`| ${codeCell(entry.path)} | ${codeCell(entry.url ?? 'missing')} |`);
    }
  }

  lines.push(
    '',
    '_This audit is factual input for third-party notice review. It is not a legal conclusion._',
  );
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
    const next = argv[index + 1];
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--root') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --root');
      options.root = next;
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --output-json');
      options.outputJson = next;
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --output-md');
      options.outputMd = next;
      index += 1;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }
  return options;
}

function printHelp() {
  process.stdout.write(`Third-party notice candidate audit\n\nUsage:\n  node scripts/legal/build-third-party-notice-candidate-audit.mjs [options]\n\nOptions:\n  --root <path>         Repository root (default: current working directory)\n  --output-json <path>  Write JSON report\n  --output-md <path>    Write Markdown report\n  --help, -h            Show this help\n`);
}

export function run(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }

  const rootDir = path.resolve(options.root);
  const audit = buildThirdPartyNoticeCandidateAudit({
    trackedFiles: listTrackedFiles(rootDir),
    submodules: listSubmodules(rootDir),
    gitHeadSha: resolveGitHeadSha(rootDir),
    generatedAt: resolveGeneratedAt(),
  });

  if (options.outputJson) {
    const outputPath = path.resolve(rootDir, options.outputJson);
    fs.mkdirSync(path.dirname(outputPath), { recursive: true });
    fs.writeFileSync(outputPath, `${JSON.stringify(audit, null, 2)}\n`);
  }
  if (options.outputMd) {
    const outputPath = path.resolve(rootDir, options.outputMd);
    fs.mkdirSync(path.dirname(outputPath), { recursive: true });
    fs.writeFileSync(outputPath, renderMarkdownReport(audit));
  }
  if (!options.outputJson && !options.outputMd) {
    process.stdout.write(`${JSON.stringify(audit, null, 2)}\n`);
  }
  return 0;
}

const executedAsMain = import.meta.url === pathToFileURL(path.resolve(process.argv[1] || '')).href;
if (executedAsMain) {
  try {
    process.exitCode = run(process.argv);
  } catch (error) {
    process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}
