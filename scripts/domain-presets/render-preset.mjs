#!/usr/bin/env node
import { existsSync, lstatSync, mkdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';

const DEFAULT_PRESET = 'templates/domain-presets/web-api-bff/preset.json';
const DEFAULT_OUTPUT_JSON = 'artifacts/domain-presets/domain-preset-report.json';
const DEFAULT_OUTPUT_MD = 'artifacts/domain-presets/domain-preset-report.md';
const RFC3339_DATE_TIME_PATTERN = /^(?<year>\d{4})-(?<month>\d{2})-(?<day>\d{2})T(?<hour>\d{2}):(?<minute>\d{2}):(?<second>\d{2})(?<fraction>\.\d+)?(?<offset>Z|[+-]\d{2}:\d{2})$/u;

function usage() {
  process.stdout.write(`Usage: node scripts/domain-presets/render-preset.mjs [options]\n\nOptions:\n  --preset <path>              Domain assurance preset JSON (default: ${DEFAULT_PRESET}).\n  --project-root, --work <path> Repository root for path containment (default: .).\n  --generated-at <iso-date>     Deterministic generatedAt timestamp.\n  --output-json <path>          Output JSON path (default: ${DEFAULT_OUTPUT_JSON}).\n  --output-md <path>            Output Markdown path (default: ${DEFAULT_OUTPUT_MD}).\n  --no-write                    Validate and render in memory without writing outputs.\n  --help                        Show this help.\n\nThe renderer is offline-only. It reads local preset templates, never calls live external APIs, and emits report-only adoption guidance.\n`);
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
    preset: DEFAULT_PRESET,
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
    if (arg === '--preset') {
      options.preset = requireValue(argv, index, arg);
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
    preset: assertProjectContainedPath(projectRoot, options.preset, '--preset'),
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
  if (!rawPath) return null;
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

function toPosix(value) {
  return String(value).split(path.sep).join('/');
}

function displayPath(filePath, rootDir = process.cwd()) {
  if (!filePath) return null;
  const root = path.resolve(rootDir);
  const resolved = path.resolve(root, filePath);
  const relative = path.relative(root, resolved);
  return toPosix(relative && !relative.startsWith('..') && !path.isAbsolute(relative) ? relative : resolved);
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

function asArray(value) {
  return Array.isArray(value) ? value : [];
}

function compactPreset(preset) {
  if (preset?.schemaVersion !== 'domain-assurance-preset/v1') {
    throw new Error(`preset schemaVersion must be domain-assurance-preset/v1: ${preset?.schemaVersion ?? '(missing)'}`);
  }
  if (preset?.reportOnly !== true) {
    throw new Error('preset reportOnly must be true');
  }
  return {
    id: preset.id,
    title: preset.title,
    version: preset.version,
    targetUser: preset.targetUser,
    fit: preset.fit,
    startingCommand: preset.startingCommand,
    requiredInputs: asArray(preset.requiredInputs),
    defaultVerificationCommands: asArray(preset.defaultVerificationCommands),
    expectedArtifacts: asArray(preset.expectedArtifacts),
    evidenceSurfaces: asArray(preset.evidenceSurfaces),
    escalationRule: preset.escalationRule,
    referenceFlowLinks: asArray(preset.referenceFlowLinks),
    integration: preset.integration,
    reuseContracts: asArray(preset.reuseContracts),
    reportOnly: true,
  };
}

function buildReport(options, preset) {
  const compact = compactPreset(preset);
  const requiredArtifactCount = compact.expectedArtifacts.filter((artifact) => artifact?.required === true).length;
  return {
    schemaVersion: 'domain-assurance-preset-report/v1',
    generatedAt: options.generatedAt ?? new Date().toISOString(),
    source: 'offline-domain-preset-template',
    preset: compact,
    summary: {
      startingCommand: compact.startingCommand.command,
      requiredInputCount: compact.requiredInputs.length,
      verificationCommandCount: compact.defaultVerificationCommands.length,
      expectedArtifactCount: compact.expectedArtifacts.length,
      requiredArtifactCount,
      evidenceSurfaceCount: compact.evidenceSurfaces.length,
      escalationRequiresHumanDecision: compact.escalationRule.requiredHumanDecision === true,
      contextPackRequired: compact.integration.contextPackRequired === true,
      execPlanRequired: compact.integration.execPlanRequired === true,
    },
    collectionBoundaries: {
      externalApisCalled: false,
      generatedFromLocalTemplate: true,
      approvalAuthority: 'human maintainer; preset output is guidance and evidence routing only',
      reportOnlyReason: 'Domain presets select inputs, commands, and evidence surfaces; they do not approve, merge, or change policy-gate enforcement.',
    },
  };
}

function escapeMd(value) {
  return String(value ?? '')
    .replaceAll('\\', '\\\\')
    .replaceAll('|', '\\|')
    .replaceAll('\n', '<br>');
}

function renderList(values) {
  return asArray(values).map((value) => `- ${value}`).join('\n');
}

function renderMarkdown(report) {
  const preset = report.preset;
  return `# Domain Assurance Preset: ${preset.title}\n\n` +
    `- presetId: \`${preset.id}\`\n` +
    `- generatedAt: \`${report.generatedAt}\`\n` +
    `- classification: \`${preset.fit.classification}\`\n` +
    `- reportOnly: \`${preset.reportOnly}\`\n` +
    `- startingCommand: \`${escapeMd(preset.startingCommand.command)}\`\n\n` +
    `## Target user\n\n${preset.targetUser}\n\n` +
    `## Recommended when\n\n${renderList(preset.fit.recommendedWhen)}\n\n` +
    `## Not recommended when\n\n${renderList(preset.fit.notRecommendedWhen)}\n\n` +
    `## Required inputs\n\n` +
    `| ID | Input | Path pattern | Contract |\n| --- | --- | --- | --- |\n` +
    `${preset.requiredInputs.map((input) => `| ${escapeMd(input.id)} | ${escapeMd(input.name)} | ${escapeMd(input.pathPattern)} | ${escapeMd(input.contract ?? 'n/a')} |`).join('\n')}\n\n` +
    `## Verification commands\n\n` +
    `| ID | Command | Purpose |\n| --- | --- | --- |\n` +
    `${preset.defaultVerificationCommands.map((command) => `| ${escapeMd(command.id)} | \`${escapeMd(command.command)}\` | ${escapeMd(command.purpose)} |`).join('\n')}\n\n` +
    `## Expected artifacts\n\n` +
    `| ID | Path | Required | Review purpose |\n| --- | --- | --- | --- |\n` +
    `${preset.expectedArtifacts.map((artifact) => `| ${escapeMd(artifact.id)} | ${escapeMd(artifact.path)} | ${artifact.required ? 'yes' : 'no'} | ${escapeMd(artifact.reviewPurpose)} |`).join('\n')}\n\n` +
    `## Escalation rule\n\n` +
    `- trigger: ${escapeMd(preset.escalationRule.trigger)}\n` +
    `- action: ${escapeMd(preset.escalationRule.action)}\n` +
    `- human decision required: ${preset.escalationRule.requiredHumanDecision ? 'yes' : 'no'}\n\n` +
    `## Reused contracts\n\n${renderList(preset.reuseContracts)}\n\n` +
    `## Boundaries\n\n` +
    `- ${report.collectionBoundaries.reportOnlyReason}\n` +
    `- No live external APIs were called.\n`;
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
  const preset = readJson(options.preset);
  const report = buildReport(options, preset);
  const markdown = renderMarkdown(report);
  if (!options.noWrite) {
    const outputJson = ensureProjectContainedOutputPath(options.projectRoot, options.outputJson, '--output-json');
    const outputMd = ensureProjectContainedOutputPath(options.projectRoot, options.outputMd, '--output-md');
    writeJson(outputJson, report);
    writeText(outputMd, markdown);
    process.stdout.write(`Domain preset report written.\n- preset: ${preset.id}\n- json: ${displayPath(options.outputJson, options.projectRoot)}\n- markdown: ${displayPath(options.outputMd, options.projectRoot)}\n`);
    return;
  }
  process.stdout.write(`Domain preset report validated without writing files.\n- preset: ${preset.id}\n- json (not written): ${displayPath(options.outputJson, options.projectRoot)}\n- markdown (not written): ${displayPath(options.outputMd, options.projectRoot)}\n`);
}

function isCliEntrypoint() {
  return Boolean(process.argv[1]) && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href;
}

if (isCliEntrypoint()) {
  try {
    main();
  } catch (error) {
    process.stderr.write(`Domain preset rendering failed: ${messageOf(error)}\n`);
    process.exit(1);
  }
}

export {
  buildReport,
  parseArgs,
  renderMarkdown,
};
