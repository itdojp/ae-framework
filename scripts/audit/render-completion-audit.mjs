#!/usr/bin/env node
import { existsSync, lstatSync, mkdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_INPUT = 'fixtures/audit/completion/pr-3566-closeout.input.json';
const DEFAULT_OUTPUT_JSON = 'artifacts/audit/completion-audit-report.json';
const DEFAULT_OUTPUT_MD = 'artifacts/audit/completion-audit-report.md';
const REPORT_SCHEMA = 'schema/completion-audit-report.schema.json';
const RFC3339_DATE_TIME_PATTERN = /^(?<year>\d{4})-(?<month>\d{2})-(?<day>\d{2})T(?<hour>\d{2}):(?<minute>\d{2}):(?<second>\d{2})(?<fraction>\.\d+)?(?<offset>Z|[+-]\d{2}:\d{2})$/u;

function usage() {
  process.stdout.write(`Usage: node scripts/audit/render-completion-audit.mjs [options]\n\nOptions:\n  --input <path>                Completion audit input JSON (default: ${DEFAULT_INPUT}).\n  --project-root, --work <path> Repository root for path containment (default: .).\n  --generated-at <iso-date>     Deterministic generatedAt timestamp.\n  --output-json <path>          Output JSON path (default: ${DEFAULT_OUTPUT_JSON}).\n  --output-md <path>            Output Markdown path (default: ${DEFAULT_OUTPUT_MD}).\n  --no-write                    Validate and render in memory without writing outputs.\n  --help                        Show this help.\n\nThe renderer is offline-only. It separates required merge checks from advisory workflow findings, skipped runs, stale runs, and local verification evidence.\n`);
}

function requireValue(argv, index, flag) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`${flag} requires a value`);
  }
  return next;
}

function isLeapYear(year) {
  return year % 4 === 0 && (year % 100 !== 0 || year % 400 === 0);
}

function daysInMonth(year, month) {
  return [31, isLeapYear(year) ? 29 : 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][month - 1] ?? 0;
}

function ensureDateTime(value, flag = 'date-time') {
  const raw = String(value ?? '').trim();
  const match = RFC3339_DATE_TIME_PATTERN.exec(raw);
  if (!match?.groups) {
    throw new Error(`${flag} must be a valid RFC3339 date-time: ${raw || '(empty)'}`);
  }
  const year = Number.parseInt(match.groups.year, 10);
  const month = Number.parseInt(match.groups.month, 10);
  const day = Number.parseInt(match.groups.day, 10);
  const hour = Number.parseInt(match.groups.hour, 10);
  const minute = Number.parseInt(match.groups.minute, 10);
  const second = Number.parseInt(match.groups.second, 10);
  if (month < 1 || month > 12 || day < 1 || day > daysInMonth(year, month) || hour > 23 || minute > 59 || second > 59) {
    throw new Error(`${flag} must be a valid RFC3339 date-time: ${raw}`);
  }
  const offset = match.groups.offset;
  if (offset !== 'Z') {
    const offsetHour = Number.parseInt(offset.slice(1, 3), 10);
    const offsetMinute = Number.parseInt(offset.slice(4, 6), 10);
    if (offsetHour > 23 || offsetMinute > 59) {
      throw new Error(`${flag} must be a valid RFC3339 date-time: ${raw}`);
    }
  }
  const timestamp = Date.parse(raw);
  if (!Number.isFinite(timestamp)) {
    throw new Error(`${flag} must be a valid RFC3339 date-time: ${raw}`);
  }
  return new Date(timestamp).toISOString();
}

function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    projectRoot: '.',
    input: DEFAULT_INPUT,
    generatedAt: null,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    noWrite: false,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--no-write') {
      options.noWrite = true;
      continue;
    }
    if (arg === '--project-root' || arg === '--work') {
      options.projectRoot = requireValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--input') {
      options.input = requireValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = ensureDateTime(requireValue(argv, index, arg), arg);
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = requireValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = requireValue(argv, index, arg);
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (options.help) return options;
  const projectRoot = path.resolve(options.projectRoot || '.');
  return {
    ...options,
    projectRoot,
    input: assertProjectContainedPath(projectRoot, options.input, '--input'),
    outputJson: assertProjectContainedPath(projectRoot, options.outputJson, '--output-json'),
    outputMd: assertProjectContainedPath(projectRoot, options.outputMd, '--output-md'),
  };
}

function isPathWithin(parentPath, childPath) {
  const relative = path.relative(path.resolve(parentPath), path.resolve(childPath));
  return relative === '' || (relative !== '' && !relative.startsWith('..') && !path.isAbsolute(relative));
}

function lstatIfExists(filePath) {
  try {
    return lstatSync(filePath);
  } catch (error) {
    if (error?.code === 'ENOENT') return null;
    throw error;
  }
}

function realpathIfExists(filePath) {
  try {
    return realpathSync.native(filePath);
  } catch (error) {
    if (error?.code === 'ENOENT') return null;
    throw error;
  }
}

function nearestExistingAncestor(filePath) {
  let cursor = path.resolve(filePath);
  while (!lstatIfExists(cursor)) {
    const parent = path.dirname(cursor);
    if (parent === cursor) return null;
    cursor = parent;
  }
  return cursor;
}

function assertProjectContainedPath(projectRoot, filePath, label) {
  const root = path.resolve(projectRoot);
  const rawPath = String(filePath ?? '').trim();
  if (!rawPath) {
    throw new Error(`${label} requires a non-empty path`);
  }
  const resolved = path.resolve(root, rawPath);
  if (!isPathWithin(root, resolved)) {
    throw new Error(`${label} must stay within --project-root: ${filePath}`);
  }
  const existingAncestor = nearestExistingAncestor(resolved);
  if (!existingAncestor) return resolved;
  const realRoot = existsSync(root) ? realpathSync.native(root) : root;
  const realAncestor = realpathIfExists(existingAncestor);
  if (realAncestor && !isPathWithin(realRoot, realAncestor)) {
    throw new Error(`${label} resolves outside --project-root: ${filePath}`);
  }
  return resolved;
}

function ensureProjectContainedOutputPath(projectRoot, filePath, label) {
  const resolved = assertProjectContainedPath(projectRoot, filePath, label);
  const outputStat = lstatIfExists(resolved);
  if (outputStat?.isSymbolicLink()) {
    throw new Error(`${label} must not be a symbolic link: ${filePath}`);
  }
  const outputDir = path.dirname(resolved);
  const existingAncestor = nearestExistingAncestor(outputDir);
  if (!existingAncestor) {
    throw new Error(`${label} has no existing ancestor under --project-root: ${filePath}`);
  }
  const realProjectRoot = realpathSync.native(path.resolve(projectRoot));
  const realAncestor = realpathIfExists(existingAncestor);
  if (!realAncestor || !isPathWithin(realProjectRoot, realAncestor)) {
    throw new Error(`${label} output directory resolves outside --project-root: ${filePath}`);
  }
  mkdirSync(outputDir, { recursive: true });
  const realOutputDir = realpathSync.native(outputDir);
  if (!isPathWithin(realProjectRoot, realOutputDir)) {
    throw new Error(`${label} output directory resolves outside --project-root: ${filePath}`);
  }
  const outputStatAfterMkdir = lstatIfExists(resolved);
  if (outputStatAfterMkdir?.isSymbolicLink()) {
    throw new Error(`${label} must not be a symbolic link: ${filePath}`);
  }
  return resolved;
}

function readJson(filePath) {
  return JSON.parse(readFileSync(filePath, 'utf8'));
}

function writeJson(filePath, payload) {
  writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
}

function writeText(filePath, content) {
  writeFileSync(filePath, content, 'utf8');
}

function optionalArray(value, label) {
  if (value === undefined) return [];
  if (!Array.isArray(value)) {
    throw new Error(`${label} must be an array`);
  }
  return value;
}

function requireObject(value, label) {
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    throw new Error(`${label} must be an object`);
  }
  return value;
}

function requireString(value, label) {
  if (typeof value !== 'string' || value.trim().length === 0) {
    throw new Error(`${label} must be a non-empty string`);
  }
  return value;
}

function requireBoolean(value, label) {
  if (typeof value !== 'boolean') {
    throw new Error(`${label} must be a boolean`);
  }
  return value;
}

function requireArray(value, label) {
  if (!Array.isArray(value)) {
    throw new Error(`${label} must be an array`);
  }
  return value;
}

function requireConst(value, expected, label) {
  if (value !== expected) {
    throw new Error(`${label} must be ${JSON.stringify(expected)}`);
  }
  return expected;
}

function requireAllowed(value, allowed, label) {
  if (!allowed.includes(value)) {
    throw new Error(`${label} must be one of: ${allowed.join(', ')}`);
  }
  return value;
}

function validateTimestampOrNull(value, label) {
  if (value === null || value === undefined) return null;
  return ensureDateTime(value, label);
}

function normalizeSubject(subject) {
  const input = requireObject(subject, 'subject');
  const pullRequest = requireObject(input.pullRequest, 'subject.pullRequest');
  const state = requireAllowed(pullRequest.state, ['open', 'closed', 'merged'], 'subject.pullRequest.state');
  return {
    repository: requireString(input.repository, 'subject.repository'),
    pullRequest: {
      number: Number.parseInt(String(pullRequest.number), 10),
      url: requireString(pullRequest.url, 'subject.pullRequest.url'),
      title: requireString(pullRequest.title, 'subject.pullRequest.title'),
      state,
      headSha: requireString(pullRequest.headSha, 'subject.pullRequest.headSha'),
      mergedAt: validateTimestampOrNull(pullRequest.mergedAt, 'subject.pullRequest.mergedAt'),
      mergeCommit: pullRequest.mergeCommit === null ? null : requireString(pullRequest.mergeCommit, 'subject.pullRequest.mergeCommit'),
    },
    issueRefs: requireArray(input.issueRefs, 'subject.issueRefs').map((issueRef, index) => {
      const issue = requireObject(issueRef, `subject.issueRefs[${index}]`);
      return {
        number: Number.parseInt(String(issue.number), 10),
        url: requireString(issue.url, `subject.issueRefs[${index}].url`),
        role: requireString(issue.role, `subject.issueRefs[${index}].role`),
      };
    }),
  };
}

function normalizeCheck(check, label) {
  const input = requireObject(check, label);
  return {
    id: requireString(input.id, `${label}.id`),
    name: requireString(input.name, `${label}.name`),
    workflow: requireString(input.workflow, `${label}.workflow`),
    required: requireConst(input.required, true, `${label}.required`),
    status: requireAllowed(input.status, ['pass', 'fail', 'pending', 'skipped', 'cancelled', 'warning'], `${label}.status`),
    url: requireString(input.url, `${label}.url`),
    headSha: requireString(input.headSha, `${label}.headSha`),
    startedAt: validateTimestampOrNull(input.startedAt, `${label}.startedAt`),
    completedAt: validateTimestampOrNull(input.completedAt, `${label}.completedAt`),
  };
}

function normalizeAdvisoryRun(run, label) {
  const input = requireObject(run, label);
  return {
    id: requireString(input.id, `${label}.id`),
    name: requireString(input.name, `${label}.name`),
    workflow: requireString(input.workflow, `${label}.workflow`),
    required: requireConst(input.required, false, `${label}.required`),
    status: requireAllowed(input.status, ['pass', 'fail', 'pending', 'skipped', 'cancelled', 'warning'], `${label}.status`),
    severity: requireAllowed(input.severity, ['info', 'warning', 'action-required'], `${label}.severity`),
    url: requireString(input.url, `${label}.url`),
    headSha: requireString(input.headSha, `${label}.headSha`),
    blocking: requireConst(input.blocking, false, `${label}.blocking`),
    finding: requireString(input.finding, `${label}.finding`),
  };
}

function normalizeSkippedRun(run, label) {
  const input = requireObject(run, label);
  return {
    id: requireString(input.id, `${label}.id`),
    name: requireString(input.name, `${label}.name`),
    workflow: requireString(input.workflow, `${label}.workflow`),
    status: requireConst(input.status, 'skipped', `${label}.status`),
    reason: requireString(input.reason, `${label}.reason`),
    url: requireString(input.url, `${label}.url`),
  };
}

function normalizeStaleRun(run, label) {
  const input = requireObject(run, label);
  return {
    id: requireString(input.id, `${label}.id`),
    name: requireString(input.name, `${label}.name`),
    workflow: requireString(input.workflow, `${label}.workflow`),
    status: requireAllowed(input.status, ['cancelled', 'fail', 'stale'], `${label}.status`),
    headSha: requireString(input.headSha, `${label}.headSha`),
    url: requireString(input.url, `${label}.url`),
    resolution: requireString(input.resolution, `${label}.resolution`),
  };
}

function normalizeLocalVerification(item, label) {
  const input = requireObject(item, label);
  return {
    id: requireString(input.id, `${label}.id`),
    command: requireString(input.command, `${label}.command`),
    status: requireAllowed(input.status, ['pass', 'fail', 'not-run'], `${label}.status`),
    artifactPaths: requireArray(input.artifactPaths, `${label}.artifactPaths`).map((artifactPath, index) => requireString(artifactPath, `${label}.artifactPaths[${index}]`)),
    note: requireString(input.note, `${label}.note`),
  };
}

function normalizeAuditNote(note, label) {
  const input = requireObject(note, label);
  return {
    id: requireString(input.id, `${label}.id`),
    severity: requireAllowed(input.severity, ['info', 'warning', 'action-required'], `${label}.severity`),
    category: requireString(input.category, `${label}.category`),
    message: requireString(input.message, `${label}.message`),
    ...(input.relatedUrl === undefined ? {} : { relatedUrl: input.relatedUrl === null ? null : requireString(input.relatedUrl, `${label}.relatedUrl`) }),
  };
}

function assertRequiredChecksMatchFinalHead(requiredMergeChecks, finalHeadSha) {
  for (const [index, check] of requiredMergeChecks.entries()) {
    if (check.headSha !== finalHeadSha) {
      throw new Error(`requiredMergeChecks[${index}].headSha must match subject.pullRequest.headSha`);
    }
  }
}

function normalizeCollectionBoundaries(boundaries) {
  const input = requireObject(boundaries, 'collectionBoundaries');
  return {
    liveGitHubApiCalled: requireConst(input.liveGitHubApiCalled, false, 'collectionBoundaries.liveGitHubApiCalled'),
    generatedFromLocalFixture: requireBoolean(input.generatedFromLocalFixture, 'collectionBoundaries.generatedFromLocalFixture'),
    approvalAuthority: requireString(input.approvalAuthority, 'collectionBoundaries.approvalAuthority'),
    requiredCheckSource: requireString(input.requiredCheckSource, 'collectionBoundaries.requiredCheckSource'),
    advisoryFindingSource: requireString(input.advisoryFindingSource, 'collectionBoundaries.advisoryFindingSource'),
    reportOnlyReason: requireString(input.reportOnlyReason, 'collectionBoundaries.reportOnlyReason'),
  };
}

function buildConclusion({ subject, requiredMergeChecks, advisoryWorkflowRuns, staleWorkflowRuns, localVerification }) {
  const requiredChecksPassed = requiredMergeChecks.length > 0 && requiredMergeChecks.every((check) => check.status === 'pass');
  const advisoryFindingsPresent = advisoryWorkflowRuns.length > 0;
  const staleRunsPresent = staleWorkflowRuns.length > 0;
  const localVerificationPassed = localVerification.length > 0 && localVerification.every((item) => item.status === 'pass');
  const merged = subject.pullRequest.state === 'merged';

  let status = 'blocked';
  if (requiredChecksPassed && merged && advisoryFindingsPresent) {
    status = 'merged-with-advisory-findings';
  } else if (requiredChecksPassed && merged && staleRunsPresent) {
    status = 'merged-with-stale-runs';
  } else if (requiredChecksPassed) {
    status = 'required-passed';
  }

  const summary = requiredChecksPassed
    ? `Required merge checks passed for PR #${subject.pullRequest.number}; advisory workflow findings, skipped runs, and stale runs are recorded separately and do not represent approval authority.`
    : `PR #${subject.pullRequest.number} is not complete because at least one required merge check is not passing.`;

  return {
    status,
    summary,
    requiredChecksPassed,
    advisoryFindingsPresent,
    staleRunsPresent,
    localVerificationPassed,
    mergeApprovedByAudit: false,
  };
}

function buildReport(options, input) {
  requireObject(input, 'completion audit input');
  if (input.schemaVersion !== 'completion-audit-input/v1') {
    throw new Error(`schemaVersion must be completion-audit-input/v1: ${input.schemaVersion ?? '(missing)'}`);
  }
  const subject = normalizeSubject(input.subject);
  const requiredMergeChecks = requireArray(input.requiredMergeChecks, 'requiredMergeChecks').map((check, index) => normalizeCheck(check, `requiredMergeChecks[${index}]`));
  assertRequiredChecksMatchFinalHead(requiredMergeChecks, subject.pullRequest.headSha);
  const advisoryWorkflowRuns = optionalArray(input.advisoryWorkflowRuns, 'advisoryWorkflowRuns').map((run, index) => normalizeAdvisoryRun(run, `advisoryWorkflowRuns[${index}]`));
  const skippedWorkflowRuns = optionalArray(input.skippedWorkflowRuns, 'skippedWorkflowRuns').map((run, index) => normalizeSkippedRun(run, `skippedWorkflowRuns[${index}]`));
  const staleWorkflowRuns = optionalArray(input.staleWorkflowRuns, 'staleWorkflowRuns').map((run, index) => normalizeStaleRun(run, `staleWorkflowRuns[${index}]`));
  const localVerification = optionalArray(input.localVerification, 'localVerification').map((item, index) => normalizeLocalVerification(item, `localVerification[${index}]`));
  const auditNotes = requireArray(input.auditNotes, 'auditNotes').map((note, index) => normalizeAuditNote(note, `auditNotes[${index}]`));
  const collectionBoundaries = normalizeCollectionBoundaries(input.collectionBoundaries);
  const conclusion = buildConclusion({ subject, requiredMergeChecks, advisoryWorkflowRuns, staleWorkflowRuns, localVerification });

  return {
    schemaVersion: 'completion-audit-report/v1',
    reportOnly: true,
    generatedAt: options.generatedAt ?? new Date().toISOString(),
    source: input.source === 'manual-completion-audit-input' ? 'manual-completion-audit-input' : 'offline-completion-audit-fixture',
    subject,
    conclusion,
    summary: {
      requiredCheckCount: requiredMergeChecks.length,
      requiredChecksPassedCount: requiredMergeChecks.filter((check) => check.status === 'pass').length,
      advisoryWorkflowFindingCount: advisoryWorkflowRuns.length,
      skippedWorkflowRunCount: skippedWorkflowRuns.length,
      staleWorkflowRunCount: staleWorkflowRuns.length,
      localVerificationCount: localVerification.length,
      auditNoteCount: auditNotes.length,
    },
    requiredMergeChecks,
    advisoryWorkflowRuns,
    skippedWorkflowRuns,
    staleWorkflowRuns,
    localVerification,
    auditNotes,
    collectionBoundaries,
  };
}

function formatJsonPath(instancePath) {
  if (!instancePath) return 'report';
  return `report${instancePath.split('/').slice(1).map((segment) => {
    const unescaped = segment.replaceAll('~1', '/').replaceAll('~0', '~');
    return /^[A-Za-z_$][\w$]*$/u.test(unescaped) ? `.${unescaped}` : `[${JSON.stringify(unescaped)}]`;
  }).join('')}`;
}

function formatSchemaError(error) {
  const location = formatJsonPath(error.instancePath ?? '');
  if (error.keyword === 'required' && error.params?.missingProperty) {
    return `${location} must include required property ${JSON.stringify(error.params.missingProperty)}`;
  }
  if (error.keyword === 'additionalProperties' && error.params?.additionalProperty) {
    return `${location} must not include additional property ${JSON.stringify(error.params.additionalProperty)}`;
  }
  return `${location} ${error.message ?? 'is invalid'}`;
}

function validateReportSchema(report, projectRoot) {
  const schemaPath = path.join(projectRoot, REPORT_SCHEMA);
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(readJson(schemaPath));
  if (!validate(report)) {
    const details = (validate.errors ?? []).slice(0, 8).map(formatSchemaError).join('; ');
    throw new Error(`Completion audit report does not match ${REPORT_SCHEMA}: ${details}`);
  }
}

function escapeMd(value) {
  return String(value ?? '')
    .replaceAll('\\', '\\\\')
    .replaceAll('|', '\\|')
    .replaceAll('\n', '<br>');
}

function renderLinkedLabel(label, url) {
  const text = escapeMd(label);
  return url ? `[${text}](${url})` : text;
}

function renderRows(values, emptyMessage, renderRow) {
  if (values.length === 0) return `_${emptyMessage}_\n`;
  return `${values.map(renderRow).join('\n')}\n`;
}

function renderMarkdown(report) {
  const pr = report.subject.pullRequest;
  return `# Completion Audit Report: PR #${pr.number}\n\n`
    + `- schemaVersion: \`${report.schemaVersion}\`\n`
    + `- generatedAt: \`${report.generatedAt}\`\n`
    + `- repository: \`${report.subject.repository}\`\n`
    + `- pullRequest: ${renderLinkedLabel(`#${pr.number} ${pr.title}`, pr.url)}\n`
    + `- conclusion: \`${report.conclusion.status}\`\n`
    + `- reportOnly: \`${report.reportOnly}\`\n\n`
    + `## Conclusion\n\n${report.conclusion.summary}\n\n`
    + `| Signal | Value |\n| --- | --- |\n`
    + `| Required checks passed | ${report.conclusion.requiredChecksPassed ? 'yes' : 'no'} |\n`
    + `| Advisory findings present | ${report.conclusion.advisoryFindingsPresent ? 'yes' : 'no'} |\n`
    + `| Stale runs present | ${report.conclusion.staleRunsPresent ? 'yes' : 'no'} |\n`
    + `| Local verification passed | ${report.conclusion.localVerificationPassed ? 'yes' : 'no'} |\n`
    + `| Audit grants approval | ${report.conclusion.mergeApprovedByAudit ? 'yes' : 'no'} |\n\n`
    + `## Required merge checks\n\n| Check | Workflow | Status | Head | Link |\n| --- | --- | --- | --- | --- |\n`
    + renderRows(report.requiredMergeChecks, 'No required merge checks recorded.', (check) => `| ${escapeMd(check.name)} | ${escapeMd(check.workflow)} | ${escapeMd(check.status)} | \`${escapeMd(check.headSha.slice(0, 12))}\` | ${renderLinkedLabel('run', check.url)} |`)
    + `\n## Advisory workflow findings\n\n| Finding | Workflow | Severity | Status | Blocking | Link |\n| --- | --- | --- | --- | --- | --- |\n`
    + renderRows(report.advisoryWorkflowRuns, 'No advisory workflow findings recorded.', (run) => `| ${escapeMd(run.finding)} | ${escapeMd(run.workflow)} / ${escapeMd(run.name)} | ${escapeMd(run.severity)} | ${escapeMd(run.status)} | ${run.blocking ? 'yes' : 'no'} | ${renderLinkedLabel('source', run.url)} |`)
    + `\n## Skipped workflow runs\n\n| Run | Reason | Link |\n| --- | --- | --- |\n`
    + renderRows(report.skippedWorkflowRuns, 'No skipped workflow runs recorded.', (run) => `| ${escapeMd(run.workflow)} / ${escapeMd(run.name)} | ${escapeMd(run.reason)} | ${renderLinkedLabel('source', run.url)} |`)
    + `\n## Stale workflow runs\n\n| Run | Status | Stale head | Resolution | Link |\n| --- | --- | --- | --- | --- |\n`
    + renderRows(report.staleWorkflowRuns, 'No stale workflow runs recorded.', (run) => `| ${escapeMd(run.workflow)} / ${escapeMd(run.name)} | ${escapeMd(run.status)} | \`${escapeMd(run.headSha.slice(0, 12))}\` | ${escapeMd(run.resolution)} | ${renderLinkedLabel('run', run.url)} |`)
    + `\n## Local verification\n\n| ID | Command | Status | Note |\n| --- | --- | --- | --- |\n`
    + renderRows(report.localVerification, 'No local verification recorded.', (item) => `| ${escapeMd(item.id)} | \`${escapeMd(item.command)}\` | ${escapeMd(item.status)} | ${escapeMd(item.note)} |`)
    + `\n## Audit notes\n\n| ID | Severity | Category | Message |\n| --- | --- | --- | --- |\n`
    + renderRows(report.auditNotes, 'No audit notes recorded.', (note) => `| ${escapeMd(note.id)} | ${escapeMd(note.severity)} | ${escapeMd(note.category)} | ${escapeMd(note.message)} |`)
    + `\n## Collection boundaries\n\n`
    + `- Live GitHub APIs called by this renderer: ${report.collectionBoundaries.liveGitHubApiCalled ? 'yes' : 'no'}\n`
    + `- Generated from local fixture: ${report.collectionBoundaries.generatedFromLocalFixture ? 'yes' : 'no'}\n`
    + `- Approval authority: ${escapeMd(report.collectionBoundaries.approvalAuthority)}\n`
    + `- Report-only reason: ${escapeMd(report.collectionBoundaries.reportOnlyReason)}\n`;
}

function messageOf(error) {
  return error instanceof Error ? error.message : String(error);
}

function main() {
  const options = parseArgs();
  if (options.help) {
    usage();
    return;
  }
  const input = readJson(options.input);
  const report = buildReport(options, input);
  validateReportSchema(report, options.projectRoot);
  const markdown = renderMarkdown(report);
  if (!options.noWrite) {
    ensureProjectContainedOutputPath(options.projectRoot, options.outputJson, '--output-json');
    ensureProjectContainedOutputPath(options.projectRoot, options.outputMd, '--output-md');
    writeJson(options.outputJson, report);
    writeText(options.outputMd, markdown);
    process.stdout.write(`Completion audit report written.\njson: ${options.outputJson}\nmarkdown: ${options.outputMd}\nconclusion: ${report.conclusion.status}\n`);
    return;
  }
  process.stdout.write(`Completion audit report validated without writing files.\nsource: ${report.source}\nconclusion: ${report.conclusion.status}\nrequiredChecksPassed: ${report.conclusion.requiredChecksPassed}\nadvisoryFindings: ${report.summary.advisoryWorkflowFindingCount}\n`);
}

const invokedPath = process.argv[1] ? pathToFileURL(path.resolve(process.argv[1])).href : null;
if (invokedPath === import.meta.url) {
  try {
    main();
  } catch (error) {
    process.stderr.write(`${messageOf(error)}\n`);
    process.exitCode = 1;
  }
}
