#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';
import { resolveGeneratedAt } from './inventory-license-scope.mjs';

function readJsonFile(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function ensureStringArray(value, label) {
  if (!Array.isArray(value) || value.some((entry) => typeof entry !== 'string')) {
    throw new Error(`${label} must be an array of strings`);
  }
  return value;
}

function getOriginClassCount(summary, key) {
  const counts = summary?.byOriginClass;
  if (!counts || typeof counts !== 'object') {
    return 0;
  }
  const value = counts[key];
  return Number.isInteger(value) && value >= 0 ? value : 0;
}

function buildDraftNoticeLines() {
  return [
    'ae-framework',
    'Copyright (c) ae-framework contributors.',
    'This product includes software developed by the ae-framework contributors.',
  ];
}

export function buildNoticeReadinessAudit({
  scopeAudit,
  conditionalAudit,
  scopeAuditPath,
  conditionalAuditPath,
  generatedAt = new Date().toISOString(),
}) {
  const nestedNoticeFiles = ensureStringArray(scopeAudit.nestedNoticeFiles ?? [], 'nestedNoticeFiles');
  const unclassifiedConditionalFiles = (conditionalAudit.items ?? [])
    .filter((item) => item?.originClass === 'runtime-output-or-unclassified')
    .map((item) => item.path)
    .filter((value) => typeof value === 'string');

  const blockers = [];
  if (nestedNoticeFiles.length > 0) {
    blockers.push({
      code: 'nested-notice-review-required',
      reason: `${nestedNoticeFiles.length} tracked nested notice files require review before final NOTICE text is approved.`,
    });
  }
  if (unclassifiedConditionalFiles.length > 0) {
    blockers.push({
      code: 'conditional-origin-unclassified',
      reason: `${unclassifiedConditionalFiles.length} conditional assets are still unclassified and require provenance review.`,
    });
  }

  return {
    schemaVersion: 'notice-readiness-audit/v1',
    generatedAt,
    inputs: {
      scopeAuditPath,
      conditionalAuditPath,
      repositoryLicense: scopeAudit.repositoryLicense ?? null,
      packageLicenseField: scopeAudit.packageLicenseField ?? null,
      nestedNoticeFilesCount: nestedNoticeFiles.length,
      conditionalOriginClassCounts: conditionalAudit.summary?.byOriginClass ?? {},
    },
    evidence: {
      nestedNoticeFiles,
      unclassifiedConditionalFiles,
    },
    readiness: {
      status: blockers.length === 0 ? 'draft-ready' : 'needs-review',
      recommendedAction: blockers.length === 0 ? 'prepare-draft-only' : 'review-and-draft',
      blockers,
      cutoverPrerequisites: [
        'Review contributor and legal feasibility before changing LICENSE.',
        'Update root LICENSE and package.json license field together on cutover.',
        'Approve the root NOTICE text before publishing Apache-2.0 as the repository-standard license.',
      ],
    },
    proposedRootNotice: {
      status: 'draft-only',
      reviewRequired: true,
      title: 'ae-framework',
      lines: buildDraftNoticeLines(),
    },
  };
}

const escapeTableCell = (value) =>
  String(value ?? '')
    .replace(/\\/g, '\\\\')
    .replace(/`/g, '\\`')
    .replace(/\|/g, '\\|')
    .replace(/\r?\n/g, '<br>');

const codeCell = (value) => `\`${escapeTableCell(value)}\``;

export function renderMarkdownReport(audit) {
  const lines = [
    '# Notice Readiness Audit',
    '',
    `- generatedAt: ${audit.generatedAt}`,
    `- repository license: ${audit.inputs.repositoryLicense ?? 'missing'}`,
    `- package.json license: ${audit.inputs.packageLicenseField ?? 'missing'}`,
    `- readiness: ${audit.readiness.status}`,
    `- recommended action: ${audit.readiness.recommendedAction}`,
    '',
    '## Inputs',
    `- scope audit: ${audit.inputs.scopeAuditPath}`,
    `- conditional audit: ${audit.inputs.conditionalAuditPath}`,
    `- nested notice files: ${audit.inputs.nestedNoticeFilesCount}`,
    '',
    '## Conditional origin classes',
  ];

  for (const [originClass, count] of Object.entries(audit.inputs.conditionalOriginClassCounts)) {
    lines.push(`- ${originClass}: ${count}`);
  }

  lines.push('', '## Blockers');
  if (audit.readiness.blockers.length === 0) {
    lines.push('- none');
  } else {
    for (const blocker of audit.readiness.blockers) {
      lines.push(`- ${blocker.code}: ${blocker.reason}`);
    }
  }

  lines.push('', '## Cutover prerequisites');
  for (const prerequisite of audit.readiness.cutoverPrerequisites) {
    lines.push(`- ${prerequisite}`);
  }

  lines.push('', '## Evidence details');
  if (audit.evidence.nestedNoticeFiles.length === 0) {
    lines.push('- nestedNoticeFiles: none');
  } else {
    lines.push('| Nested notice file |', '| --- |');
    for (const filePath of audit.evidence.nestedNoticeFiles) {
      lines.push(`| ${codeCell(filePath)} |`);
    }
  }

  if (audit.evidence.unclassifiedConditionalFiles.length === 0) {
    lines.push('- unclassifiedConditionalFiles: none');
  } else {
    lines.push('', '| Unclassified conditional file |', '| --- |');
    for (const filePath of audit.evidence.unclassifiedConditionalFiles) {
      lines.push(`| ${codeCell(filePath)} |`);
    }
  }

  lines.push('', '## Proposed root NOTICE draft', '', '```text');
  for (const noticeLine of audit.proposedRootNotice.lines) {
    lines.push(noticeLine);
  }
  lines.push('```', '', '_Draft only. This text is not effective until the repository license decision is approved._');

  return `${lines.join('\n')}\n`;
}

function parseArgs(argv) {
  const options = {
    scopeAudit: 'artifacts/reference/legal/license-scope-audit.json',
    conditionalAudit: 'artifacts/reference/legal/conditional-asset-audit.json',
    outputJson: null,
    outputMd: null,
    root: process.cwd(),
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
    if (arg === '--scope-audit') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --scope-audit');
      options.scopeAudit = next;
      index += 1;
      continue;
    }
    if (arg === '--conditional-audit') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --conditional-audit');
      options.conditionalAudit = next;
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
  process.stdout.write(`Notice readiness audit

Usage:
  node scripts/legal/build-notice-readiness.mjs [options]

Options:
  --root <path>               Repository root (default: current working directory)
  --scope-audit <path>        Input JSON from license scope audit
  --conditional-audit <path>  Input JSON from conditional asset audit
  --output-json <path>        Write JSON report
  --output-md <path>          Write Markdown report
  --help, -h                  Show this help
`);
}

export function run(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }

  const rootDir = path.resolve(options.root);
  const scopeAuditPath = path.resolve(rootDir, options.scopeAudit);
  const conditionalAuditPath = path.resolve(rootDir, options.conditionalAudit);
  const audit = buildNoticeReadinessAudit({
    scopeAudit: readJsonFile(scopeAuditPath),
    conditionalAudit: readJsonFile(conditionalAuditPath),
    scopeAuditPath: path.relative(rootDir, scopeAuditPath).replace(/\\/g, '/'),
    conditionalAuditPath: path.relative(rootDir, conditionalAuditPath).replace(/\\/g, '/'),
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

const isExecutedAsMain = (() => {
  const entry = process.argv[1];
  if (!entry) return false;
  return pathToFileURL(path.resolve(entry)).href === import.meta.url;
})();

if (isExecutedAsMain) {
  try {
    process.exitCode = run();
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`${message}\n`);
    process.exitCode = 1;
  }
}
