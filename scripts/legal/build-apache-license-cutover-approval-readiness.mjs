#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { execFileSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import {
  normalizeRequiredGitHeadSha,
  resolveGeneratedAt,
  resolveGitHeadSha,
} from './inventory-license-scope.mjs';

const REQUIRED_AUDIT_KEYS = [
  ['licenseScopeAuditPath', 'artifacts/reference/legal/license-scope-audit.json'],
  ['conditionalAssetAuditPath', 'artifacts/reference/legal/conditional-asset-audit.json'],
  ['noticeReadinessAuditPath', 'artifacts/reference/legal/notice-readiness-audit.json'],
  ['contributorReadinessAuditPath', 'artifacts/reference/legal/contributor-license-readiness-audit.json'],
  ['thirdPartyNoticeCandidateAuditPath', 'artifacts/reference/legal/third-party-notice-candidate-audit.json'],
  ['cutoverReadinessAuditPath', 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json'],
];

const REQUIRED_APPROVAL_ITEMS = [
  'Contributor / relicensing authority review',
  'Root `NOTICE` text approval',
  'Trademark boundary review',
  'Third-party notice review',
  'Apache-2.0 cutover readiness audit review',
];

const CUTOVER_ALLOWED_EXACT_PATHS = new Set([
  'LICENSE',
  'NOTICE',
  'package.json',
  'README.md',
  'CONTRIBUTING.md',
  'LICENSE-SCOPE.md',
  'TRADEMARKS.md',
  'THIRD_PARTY_NOTICES.md',
  'docs/agents/commands.md',
  'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
]);

const CUTOVER_ALLOWED_PREFIXES = [
  'docs/project/',
  'artifacts/reference/legal/',
];

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

function isCutoverAllowedPath(filePath) {
  return CUTOVER_ALLOWED_EXACT_PATHS.has(filePath)
    || CUTOVER_ALLOWED_PREFIXES.some((prefix) => filePath.startsWith(prefix));
}

function listChangedFilesBetweenShas(rootDir, fromSha, toSha) {
  const output = execFileSync('git', ['diff', '--name-only', `${fromSha}..${toSha}`], {
    cwd: rootDir,
    encoding: 'utf8',
  });
  return output
    .split('\n')
    .map((line) => line.trim())
    .filter((line) => line.length > 0);
}

function getSection(markdown, heading) {
  const headingMarker = `## ${heading}`;
  const start = markdown.indexOf(headingMarker);
  if (start === -1) {
    throw new Error(`section not found: ${heading}`);
  }
  const contentStart = markdown.indexOf('\n', start);
  const nextHeadingIndex = markdown.indexOf('\n## ', contentStart + 1);
  const content = nextHeadingIndex === -1
    ? markdown.slice(contentStart + 1)
    : markdown.slice(contentStart + 1, nextHeadingIndex + 1);
  return content.trimEnd();
}

function stripInlineFormatting(value) {
  return String(value ?? '')
    .trim()
    .replace(/^`(.+)`$/u, '$1')
    .replace(/^\[(.+)\]\((.+)\)$/u, '$1');
}

function parseBulletMap(sectionText) {
  const result = {};
  for (const line of sectionText.split('\n')) {
    const match = line.match(/^-\s+(.+?):\s*(.*)$/u);
    if (!match) continue;
    result[stripInlineFormatting(match[1])] = stripInlineFormatting(match[2]);
  }
  return result;
}

function splitMarkdownTableRow(line) {
  const cells = [];
  let current = '';
  let escaped = false;

  for (let index = 1; index < line.length - 1; index += 1) {
    const character = line[index];
    if (escaped) {
      current += character;
      escaped = false;
      continue;
    }
    if (character === '\\') {
      escaped = true;
      current += character;
      continue;
    }
    if (character === '|') {
      cells.push(stripInlineFormatting(current));
      current = '';
      continue;
    }
    current += character;
  }

  cells.push(stripInlineFormatting(current));
  return cells;
}

function parseApprovalTable(sectionText) {
  const lines = sectionText
    .split('\n')
    .map((line) => line.trim())
    .filter((line) => line.startsWith('|'));
  const rows = [];
  for (const line of lines) {
    if (/^\|\s*-+\s*\|/u.test(line)) continue;
    const cells = splitMarkdownTableRow(line);
    if (cells[0] === 'Item' && cells[1] === 'Required reviewer / owner') continue;
    if (cells.length !== 5) {
      throw new Error(`approval table row is malformed: ${line}`);
    }
    rows.push({
      item: cells[0],
      requiredReviewer: cells[1],
      decision: cells[2] || 'pending',
      date: cells[3] || null,
      evidenceNote: cells[4] || null,
    });
  }
  if (rows.length === 0) {
    throw new Error('approval table rows are required');
  }
  return rows;
}

function normalizeDecision(value, fieldName) {
  const normalized = stripInlineFormatting(value).toLowerCase();
  if (normalized === '' || normalized === 'pending') return 'pending';
  if (['approved', 'approve', 'yes', 'accepted', 'ready'].includes(normalized)) return 'approved';
  if (['rejected', 'reject', 'no', 'declined', 'blocked'].includes(normalized)) return 'rejected';
  throw new Error(`${fieldName} has unsupported decision value: ${value}`);
}

function normalizeBooleanLike(value, fieldName) {
  const normalized = stripInlineFormatting(value).toLowerCase();
  if (['yes', 'true'].includes(normalized)) return true;
  if (['no', 'false'].includes(normalized)) return false;
  throw new Error(`${fieldName} must be yes/no or true/false`);
}

function escapeMarkdownCell(value) {
  return String(value ?? '')
    .replace(/\\/g, '\\\\')
    .replace(/\|/g, '\\|')
    .replace(/\n/g, '<br>');
}

function resolveAuditGitHeadSha({ cutoverReadinessAudit, gitHeadSha }) {
  const cutoverSha = normalizeRequiredGitHeadSha(cutoverReadinessAudit?.gitHeadSha, 'cutover readiness audit gitHeadSha');
  const currentGitHeadSha = gitHeadSha == null ? null : normalizeRequiredGitHeadSha(gitHeadSha, 'repository HEAD');
  if (currentGitHeadSha && currentGitHeadSha !== cutoverSha) {
    throw new Error('cutover readiness audit gitHeadSha does not match the current repository HEAD');
  }
  return currentGitHeadSha ?? cutoverSha;
}

export function parseApprovalRecord(markdown) {
  const auditBaseline = parseBulletMap(getSection(markdown, 'Audit Baseline'));
  const approvalItems = parseApprovalTable(getSection(markdown, 'Required Approval Items')).map((item) => ({
    ...item,
    normalizedDecision: normalizeDecision(item.decision, `approval row ${item.item}`),
  }));
  const decisionRecordRaw = parseBulletMap(getSection(markdown, 'Decision Record'));
  const approvedForCutoverRaw = decisionRecordRaw['approved for cutover'] ?? decisionRecordRaw['approved for cutover PR'];
  return {
    auditBaseline,
    approvalItems,
    decisionRecord: {
      overallDecision: normalizeDecision(decisionRecordRaw['overall decision'], 'overall decision'),
      approvedForCutover: normalizeBooleanLike(approvedForCutoverRaw, 'approved for cutover'),
      decisionDate: stripInlineFormatting(decisionRecordRaw['decision date']) || null,
      approvingOwner: stripInlineFormatting(decisionRecordRaw['approving owner']) || null,
      legalReviewer: stripInlineFormatting(decisionRecordRaw['legal reviewer']) || null,
      notes: stripInlineFormatting(decisionRecordRaw.notes) || null,
    },
  };
}

export function buildApacheLicenseCutoverApprovalReadinessAudit({
  approvalRecord,
  approvalRecordPath,
  cutoverReadinessAudit,
  cutoverReadinessAuditPath,
  gitHeadSha,
  changedFilesSinceApproval = [],
  generatedAt = new Date().toISOString(),
}) {
  const blockers = [];
  const auditArtifactPaths = {};
  const approvalRecordHeadSha = normalizeRequiredGitHeadSha(approvalRecord.auditBaseline['head SHA'], 'approval record head SHA');
  const cutoverReadinessGitHeadSha = normalizeRequiredGitHeadSha(cutoverReadinessAudit?.gitHeadSha, 'cutover readiness audit gitHeadSha');
  const currentGitHeadSha = resolveAuditGitHeadSha({
    cutoverReadinessAudit,
    gitHeadSha,
  });
  const normalizedChangedFiles = [...new Set(
    changedFilesSinceApproval
      .map((filePath) => String(filePath ?? '').trim())
      .filter((filePath) => filePath.length > 0),
  )].sort();
  const approvalSnapshotMatchesCurrentHead = approvalRecordHeadSha === currentGitHeadSha;
  const unexpectedChangedFilesSinceApproval = approvalSnapshotMatchesCurrentHead
    ? []
    : normalizedChangedFiles.filter((filePath) => !isCutoverAllowedPath(filePath));

  for (const [key, label] of REQUIRED_AUDIT_KEYS) {
    const value = stripInlineFormatting(approvalRecord.auditBaseline[label]);
    if (!value) {
      addBlocker(blockers, 'missing-audit-path', `${label} is missing from the approval record.`);
      auditArtifactPaths[key] = null;
    } else {
      auditArtifactPaths[key] = value;
    }
  }

  const cutoverReadinessStatus = cutoverReadinessAudit?.readiness?.status ?? null;
  if (cutoverReadinessStatus === 'blocked') {
    addBlocker(
      blockers,
      'cutover-readiness-blocked',
      'apache-license-cutover-readiness-audit/v1 is blocked and must clear factual blockers before final approval.',
    );
  }

  const approvedItems = approvalRecord.approvalItems
    .filter((item) => item.normalizedDecision === 'approved')
    .map((item) => item.item);
  const pendingItems = approvalRecord.approvalItems
    .filter((item) => item.normalizedDecision === 'pending')
    .map((item) => item.item);
  const rejectedItems = approvalRecord.approvalItems
    .filter((item) => item.normalizedDecision === 'rejected')
    .map((item) => item.item);
  const presentApprovalItems = new Set(approvalRecord.approvalItems.map((item) => item.item));
  const missingRequiredItems = REQUIRED_APPROVAL_ITEMS.filter((item) => !presentApprovalItems.has(item));

  if (rejectedItems.length > 0) {
    addBlocker(blockers, 'approval-rejected', `${rejectedItems.length} approval items are rejected.`);
  }
  if (missingRequiredItems.length > 0) {
    addBlocker(blockers, 'missing-required-approval-items', `${missingRequiredItems.length} required approval items are missing from the record.`);
  }
  if (approvalRecord.decisionRecord.overallDecision === 'rejected') {
    addBlocker(blockers, 'overall-decision-rejected', 'overall decision is rejected.');
  }
  if (approvalRecord.decisionRecord.approvedForCutover && pendingItems.length > 0) {
    addBlocker(blockers, 'approved-flag-with-pending-items', 'approved for cutover cannot be yes while approval items are still pending.');
  }
  if (approvalRecord.decisionRecord.approvedForCutover && approvalRecord.decisionRecord.overallDecision !== 'approved') {
    addBlocker(blockers, 'approved-flag-without-approved-decision', 'approved for cutover requires overall decision=approved.');
  }
  if (approvalRecord.decisionRecord.overallDecision === 'approved' && !approvalRecord.decisionRecord.approvedForCutover) {
    addBlocker(blockers, 'approved-decision-without-cutover-flag', 'overall decision approved requires approved for cutover=yes.');
  }
  if (!approvalSnapshotMatchesCurrentHead && unexpectedChangedFilesSinceApproval.length > 0) {
    addBlocker(
      blockers,
      'approval-snapshot-diverged-outside-cutover-scope',
      `approval snapshot differs from the current HEAD outside the allowed cutover scope: ${unexpectedChangedFilesSinceApproval.join(', ')}`,
    );
  }
  if (approvalRecord.decisionRecord.approvedForCutover) {
    if (!approvalRecord.decisionRecord.decisionDate) {
      addBlocker(blockers, 'missing-decision-date', 'decision date is required once the cutover is approved.');
    }
    if (!approvalRecord.decisionRecord.approvingOwner) {
      addBlocker(blockers, 'missing-approving-owner', 'approving owner is required once the cutover is approved.');
    }
    if (!approvalRecord.decisionRecord.legalReviewer) {
      addBlocker(blockers, 'missing-legal-reviewer', 'legal reviewer is required once the cutover is approved.');
    }
  }

  const status = blockers.length > 0
    ? 'blocked'
    : (pendingItems.length > 0 || !approvalRecord.decisionRecord.approvedForCutover || approvalRecord.decisionRecord.overallDecision === 'pending'
      ? 'human-review-required'
      : 'ready');
  const recommendedAction = blockers.length > 0
    ? 'resolve-record-gaps'
    : (status === 'ready' ? 'open-cutover-pr' : 'obtain-approvals');

  return {
    schemaVersion: 'apache-license-cutover-approval-readiness-audit/v1',
    generatedAt,
    gitHeadSha: currentGitHeadSha,
    inputs: {
      approvalRecordPath,
      cutoverReadinessAuditPath,
      approvalRecordHeadSha,
      cutoverReadinessGitHeadSha,
      currentGitHeadSha,
      approvalSnapshotMatchesCurrentHead,
      changedFilesSinceApproval: normalizedChangedFiles,
      unexpectedChangedFilesSinceApproval,
      auditArtifactPaths,
    },
    summary: {
      requiredApprovalCount: REQUIRED_APPROVAL_ITEMS.length,
      approvedCount: approvedItems.length,
      pendingCount: pendingItems.length,
      rejectedCount: rejectedItems.length,
      missingAuditPathCount: Object.values(auditArtifactPaths).filter((value) => value == null).length,
      changedFilesSinceApprovalCount: normalizedChangedFiles.length,
      unexpectedChangedFilesSinceApprovalCount: unexpectedChangedFilesSinceApproval.length,
      blockerCount: blockers.length,
    },
    approvalItems: approvalRecord.approvalItems,
    decisionRecord: approvalRecord.decisionRecord,
    readiness: {
      status,
      recommendedAction,
      blockers,
      pendingItems,
      approvedItems,
    },
  };
}

export function renderMarkdownReport(audit) {
  const lines = [
    '# Apache License Cutover Approval Readiness Audit',
    '',
    `- generatedAt: ${audit.generatedAt}`,
    `- gitHeadSha: ${audit.gitHeadSha}`,
    `- status: ${audit.readiness.status}`,
    `- recommended action: ${audit.readiness.recommendedAction}`,
    '',
    '## Inputs',
    `- approval record: ${audit.inputs.approvalRecordPath}`,
    `- cutover readiness audit: ${audit.inputs.cutoverReadinessAuditPath}`,
    `- approval record head SHA: ${audit.inputs.approvalRecordHeadSha}`,
    `- cutover readiness gitHeadSha: ${audit.inputs.cutoverReadinessGitHeadSha}`,
    `- current repository HEAD: ${audit.inputs.currentGitHeadSha}`,
    `- approval snapshot matches current HEAD: ${audit.inputs.approvalSnapshotMatchesCurrentHead ? 'yes' : 'no'}`,
    '',
    '## Summary',
    `- required approvals: ${audit.summary.requiredApprovalCount}`,
    `- approved: ${audit.summary.approvedCount}`,
    `- pending: ${audit.summary.pendingCount}`,
    `- rejected: ${audit.summary.rejectedCount}`,
    `- missing audit paths: ${audit.summary.missingAuditPathCount}`,
    `- changed files since approval: ${audit.summary.changedFilesSinceApprovalCount}`,
    `- unexpected changed files since approval: ${audit.summary.unexpectedChangedFilesSinceApprovalCount}`,
    `- blockers: ${audit.summary.blockerCount}`,
    '',
    '## Changed files since approval',
  ];

  if (audit.inputs.changedFilesSinceApproval.length === 0) {
    lines.push('- none');
  } else {
    for (const filePath of audit.inputs.changedFilesSinceApproval) {
      lines.push(`- ${filePath}`);
    }
  }

  lines.push('', '## Unexpected changed files since approval');
  if (audit.inputs.unexpectedChangedFilesSinceApproval.length === 0) {
    lines.push('- none');
  } else {
    for (const filePath of audit.inputs.unexpectedChangedFilesSinceApproval) {
      lines.push(`- ${filePath}`);
    }
  }

  lines.push(
    '',
    '## Approval items',
    '| Item | Required reviewer / owner | Decision | Date | Evidence / note |',
    '| --- | --- | --- | --- | --- |',
  );

  for (const item of audit.approvalItems) {
    lines.push(`| ${escapeMarkdownCell(item.item)} | ${escapeMarkdownCell(item.requiredReviewer)} | ${escapeMarkdownCell(item.decision)} | ${escapeMarkdownCell(item.date ?? '')} | ${escapeMarkdownCell(item.evidenceNote ?? '')} |`);
  }

  lines.push('', '## Blockers');
  if (audit.readiness.blockers.length === 0) {
    lines.push('- none');
  } else {
    for (const blocker of audit.readiness.blockers) {
      lines.push(`- ${blocker.code}: ${blocker.reason}`);
    }
  }

  lines.push('', '## Pending approval items');
  if (audit.readiness.pendingItems.length === 0) {
    lines.push('- none');
  } else {
    for (const item of audit.readiness.pendingItems) {
      lines.push(`- ${item}`);
    }
  }

  lines.push('', '## Approved approval items');
  if (audit.readiness.approvedItems.length === 0) {
    lines.push('- none');
  } else {
    for (const item of audit.readiness.approvedItems) {
      lines.push(`- ${item}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

function parseArgs(argv) {
  const options = {
    root: process.cwd(),
    approvalRecord: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
    cutoverReadinessAudit: 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
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
    if (arg === '--approval-record') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --approval-record');
      options.approvalRecord = next;
      index += 1;
      continue;
    }
    if (arg === '--cutover-readiness-audit') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --cutover-readiness-audit');
      options.cutoverReadinessAudit = next;
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
  process.stdout.write(`Build Apache License cutover approval readiness audit\n\nUsage:\n  node scripts/legal/build-apache-license-cutover-approval-readiness.mjs [options]\n\nOptions:\n  --root <path>                     Repository root (default: current working directory)\n  --approval-record <path>          Markdown approval record path\n  --cutover-readiness-audit <path>  apache-license-cutover-readiness-audit/v1 JSON path\n  --output-json <path>              Output JSON path\n  --output-md <path>                Output Markdown path\n  --help, -h                        Show this help\n`);
}

export function run(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }

  const rootDir = path.resolve(options.root);
  const approvalRecordPath = path.resolve(rootDir, options.approvalRecord);
  const cutoverReadinessAuditPath = path.resolve(rootDir, options.cutoverReadinessAudit);
  const outputJson = path.resolve(rootDir, options.outputJson ?? 'artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.json');
  const outputMd = path.resolve(rootDir, options.outputMd ?? 'artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.md');

  const approvalRecord = parseApprovalRecord(fs.readFileSync(approvalRecordPath, 'utf8'));
  const cutoverReadinessAudit = readJsonFile(cutoverReadinessAuditPath);
  const gitHeadSha = resolveGitHeadSha(rootDir);
  const approvalRecordHeadSha = normalizeRequiredGitHeadSha(approvalRecord.auditBaseline['head SHA'], 'approval record head SHA');
  const changedFilesSinceApproval = gitHeadSha === approvalRecordHeadSha
    ? []
    : listChangedFilesBetweenShas(rootDir, approvalRecordHeadSha, gitHeadSha);
  const generatedAt = resolveGeneratedAt();
  const audit = buildApacheLicenseCutoverApprovalReadinessAudit({
    approvalRecord,
    approvalRecordPath: relativePosix(rootDir, approvalRecordPath),
    cutoverReadinessAudit,
    cutoverReadinessAuditPath: relativePosix(rootDir, cutoverReadinessAuditPath),
    gitHeadSha,
    changedFilesSinceApproval,
    generatedAt,
  });

  fs.mkdirSync(path.dirname(outputJson), { recursive: true });
  fs.writeFileSync(outputJson, `${JSON.stringify(audit, null, 2)}\n`);
  fs.mkdirSync(path.dirname(outputMd), { recursive: true });
  fs.writeFileSync(outputMd, renderMarkdownReport(audit));
  process.stdout.write(`${JSON.stringify(audit, null, 2)}\n`);
  return 0;
}

export function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  if (!argvPath) return false;
  return importMetaUrl === pathToFileURL(path.resolve(argvPath)).href;
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  try {
    process.exit(run(process.argv));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`[apache-license-cutover-approval-readiness] ${message}\n`);
    process.exit(1);
  }
}
