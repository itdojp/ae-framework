#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';
import { normalizeRequiredGitHeadSha, resolveGeneratedAt, resolveGitHeadSha } from './inventory-license-scope.mjs';

function readJsonFile(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function relativePosix(rootDir, filePath) {
  const relative = path.relative(rootDir, filePath).replace(/\\/g, '/');
  return relative.length > 0 ? relative : '.';
}

function addBlocker(blockers, code, reason) {
  blockers.push({ code, reason });
}

function resolveCommonGitHeadSha({
  scopeAudit,
  conditionalAudit,
  noticeReadinessAudit,
  contributorReadinessAudit,
  gitHeadSha,
}) {
  const inputShas = [
    normalizeRequiredGitHeadSha(scopeAudit?.gitHeadSha, 'scope audit gitHeadSha'),
    normalizeRequiredGitHeadSha(conditionalAudit?.gitHeadSha, 'conditional audit gitHeadSha'),
    normalizeRequiredGitHeadSha(noticeReadinessAudit?.gitHeadSha, 'notice readiness audit gitHeadSha'),
    normalizeRequiredGitHeadSha(contributorReadinessAudit?.gitHeadSha, 'contributor readiness audit gitHeadSha'),
  ];
  const unique = [...new Set(inputShas)];
  if (unique.length > 1) {
    throw new Error('input audits must share the same gitHeadSha');
  }
  const currentGitHeadSha = gitHeadSha == null ? null : normalizeRequiredGitHeadSha(gitHeadSha, 'repository HEAD');
  if (currentGitHeadSha && unique[0] !== currentGitHeadSha) {
    throw new Error('input audits gitHeadSha does not match the current repository HEAD');
  }
  return currentGitHeadSha ?? unique[0];
}

export function buildApacheLicenseCutoverReadinessAudit({
  scopeAudit,
  conditionalAudit,
  noticeReadinessAudit,
  contributorReadinessAudit,
  scopeAuditPath,
  conditionalAuditPath,
  noticeReadinessAuditPath,
  contributorReadinessAuditPath,
  gitHeadSha,
  generatedAt = new Date().toISOString(),
}) {
  const blockers = [];
  const repositoryLicense = scopeAudit.repositoryLicense ?? null;
  const packageLicenseField = scopeAudit.packageLicenseField ?? null;
  const nestedNoticeFilesCount = Number.isInteger(noticeReadinessAudit?.inputs?.nestedNoticeFilesCount)
    ? noticeReadinessAudit.inputs.nestedNoticeFilesCount
    : (Array.isArray(noticeReadinessAudit?.evidence?.nestedNoticeFiles)
        ? noticeReadinessAudit.evidence.nestedNoticeFiles.length
        : (Array.isArray(scopeAudit.nestedNoticeFiles) ? scopeAudit.nestedNoticeFiles.length : 0));
  const unclassifiedConditionalFilesFromNotice = Array.isArray(noticeReadinessAudit?.evidence?.unclassifiedConditionalFiles)
    ? noticeReadinessAudit.evidence.unclassifiedConditionalFiles.length
    : 0;
  const unclassifiedConditionalFilesFromAudit = Array.isArray(conditionalAudit?.items)
    ? conditionalAudit.items.filter((item) => item?.originClass === 'runtime-output-or-unclassified').length
    : 0;
  const unclassifiedConditionalFilesCount = Math.max(
    unclassifiedConditionalFilesFromNotice,
    unclassifiedConditionalFilesFromAudit,
  );

  if (!repositoryLicense || !/mit/i.test(repositoryLicense)) {
    addBlocker(blockers, 'repository-license-baseline-missing', 'Repository LICENSE baseline is not clearly MIT before Apache-2.0 cutover review.');
  }
  if (packageLicenseField !== 'MIT') {
    addBlocker(blockers, 'package-license-field-not-mit', 'package.json license field must be explicitly MIT before Apache-2.0 cutover review.');
  }
  if (noticeReadinessAudit?.readiness?.status !== 'draft-ready') {
    addBlocker(blockers, 'notice-not-draft-ready', 'NOTICE draft readiness audit still reports unresolved review work.');
  }
  if (nestedNoticeFilesCount > 0) {
    addBlocker(blockers, 'nested-notice-review-required', `${nestedNoticeFilesCount} nested notice files still require review.`);
  }
  if (unclassifiedConditionalFilesCount > 0) {
    addBlocker(blockers, 'conditional-origin-unclassified', `${unclassifiedConditionalFilesCount} conditional assets are still unclassified.`);
  }

  const contributorSummary = contributorReadinessAudit?.summary ?? {};
  const contributorReadiness = contributorReadinessAudit?.readiness ?? {};
  const contributorHumanLikeCount = Number.isInteger(contributorSummary.humanLikeCount) ? contributorSummary.humanLikeCount : 0;
  const contributorBotLikeCount = Number.isInteger(contributorSummary.botLikeCount) ? contributorSummary.botLikeCount : 0;
  const contributorNoreplyCount = Number.isInteger(contributorSummary.noreplyCount) ? contributorSummary.noreplyCount : 0;

  const status = blockers.length > 0 ? 'blocked' : (contributorReadiness.legalDecisionRequired === false ? 'ready' : 'human-review-required');
  const recommendedAction = blockers.length > 0 ? 'resolve-blockers' : (status === 'ready' ? 'prepare-cutover-pr' : 'legal-review');
  const humanReviewReasons = status === 'ready'
    ? []
    : [
        'Repo facts do not establish relicensing authority.',
        'Contributor identities require human/legal review before relicensing approval.',
      ];
  for (const note of Array.isArray(contributorReadiness.notes) ? contributorReadiness.notes : []) {
    if (status !== 'ready' && typeof note === 'string' && note.trim().length > 0 && !humanReviewReasons.includes(note)) {
      humanReviewReasons.push(note);
    }
  }

  return {
    schemaVersion: 'apache-license-cutover-readiness-audit/v1',
    generatedAt,
    gitHeadSha: resolveCommonGitHeadSha({
      scopeAudit,
      conditionalAudit,
      noticeReadinessAudit,
      contributorReadinessAudit,
      gitHeadSha,
    }),
    inputs: {
      scopeAuditPath,
      conditionalAuditPath,
      noticeReadinessAuditPath,
      contributorReadinessAuditPath,
      repositoryLicense,
      packageLicenseField,
    },
    summary: {
      blockerCount: blockers.length,
      humanReviewRequired: status !== 'ready',
      nestedNoticeFilesCount,
      unclassifiedConditionalFilesCount,
      contributorHumanLikeCount,
      contributorBotLikeCount,
      contributorNoreplyCount,
    },
    readiness: {
      status,
      recommendedAction,
      blockers,
      humanReviewReasons,
      cutoverPrerequisites: [
        'Resolve any notice/provenance blockers before changing LICENSE.',
        'Approve the relicensing decision through human/legal review.',
        'Update root LICENSE, package.json license field, and NOTICE in the same cutover change.',
      ],
    },
  };
}
export function renderMarkdownReport(audit) {
  const lines = [
    '# Apache License Cutover Readiness Audit',
    '',
    `- generatedAt: ${audit.generatedAt}`,
    `- gitHeadSha: ${audit.gitHeadSha ?? 'missing'}`,
    `- status: ${audit.readiness.status}`,
    `- recommended action: ${audit.readiness.recommendedAction}`,
    `- repository license: ${audit.inputs.repositoryLicense ?? 'missing'}`,
    `- package.json license: ${audit.inputs.packageLicenseField ?? 'missing'}`,
    '',
    '## Inputs',
    `- scope audit: ${audit.inputs.scopeAuditPath}`,
    `- conditional audit: ${audit.inputs.conditionalAuditPath}`,
    `- notice readiness audit: ${audit.inputs.noticeReadinessAuditPath}`,
    `- contributor readiness audit: ${audit.inputs.contributorReadinessAuditPath}`,
    '',
    '## Summary',
    `- blockers: ${audit.summary.blockerCount}`,
    `- human review required: ${audit.summary.humanReviewRequired ? 'yes' : 'no'}`,
    `- nested notice files: ${audit.summary.nestedNoticeFilesCount}`,
    `- unclassified conditional files: ${audit.summary.unclassifiedConditionalFilesCount}`,
    `- contributor human-like: ${audit.summary.contributorHumanLikeCount}`,
    `- contributor bot-like: ${audit.summary.contributorBotLikeCount}`,
    `- contributor noreply: ${audit.summary.contributorNoreplyCount}`,
    '',
    '## Blockers',
  ];

  if (audit.readiness.blockers.length === 0) {
    lines.push('- none');
  } else {
    for (const blocker of audit.readiness.blockers) {
      lines.push(`- ${blocker.code}: ${blocker.reason}`);
    }
  }

  lines.push('', '## Human review reasons');
  for (const reason of audit.readiness.humanReviewReasons) {
    lines.push(`- ${reason}`);
  }

  lines.push('', '## Cutover prerequisites');
  for (const prerequisite of audit.readiness.cutoverPrerequisites) {
    lines.push(`- ${prerequisite}`);
  }

  return `${lines.join('\n')}\n`;
}

function parseArgs(argv) {
  const options = {
    root: process.cwd(),
    scopeAudit: 'artifacts/reference/legal/license-scope-audit.json',
    conditionalAudit: 'artifacts/reference/legal/conditional-asset-audit.json',
    noticeReadinessAudit: 'artifacts/reference/legal/notice-readiness-audit.json',
    contributorReadinessAudit: 'artifacts/reference/legal/contributor-license-readiness-audit.json',
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
    if (arg === '--notice-readiness-audit') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --notice-readiness-audit');
      options.noticeReadinessAudit = next;
      index += 1;
      continue;
    }
    if (arg === '--contributor-readiness-audit') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --contributor-readiness-audit');
      options.contributorReadinessAudit = next;
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
  process.stdout.write(`Apache license cutover readiness audit

Usage:
  node scripts/legal/build-apache-license-cutover-readiness.mjs [options]

Options:
  --root <path>                       Repository root (default: current working directory)
  --scope-audit <path>                Input JSON from license scope audit
  --conditional-audit <path>          Input JSON from conditional asset audit
  --notice-readiness-audit <path>     Input JSON from notice readiness audit
  --contributor-readiness-audit <path> Input JSON from contributor readiness audit
  --output-json <path>                Write JSON report
  --output-md <path>                  Write Markdown report
  --help, -h                          Show this help
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
  const noticeReadinessAuditPath = path.resolve(rootDir, options.noticeReadinessAudit);
  const contributorReadinessAuditPath = path.resolve(rootDir, options.contributorReadinessAudit);

  const audit = buildApacheLicenseCutoverReadinessAudit({
    scopeAudit: readJsonFile(scopeAuditPath),
    conditionalAudit: readJsonFile(conditionalAuditPath),
    noticeReadinessAudit: readJsonFile(noticeReadinessAuditPath),
    contributorReadinessAudit: readJsonFile(contributorReadinessAuditPath),
    scopeAuditPath: relativePosix(rootDir, scopeAuditPath),
    conditionalAuditPath: relativePosix(rootDir, conditionalAuditPath),
    noticeReadinessAuditPath: relativePosix(rootDir, noticeReadinessAuditPath),
    contributorReadinessAuditPath: relativePosix(rootDir, contributorReadinessAuditPath),
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
