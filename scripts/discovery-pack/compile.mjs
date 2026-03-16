#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import yaml from 'yaml';

import {
  DEFAULT_SOURCES,
  DISCOVERY_PACK_SECTIONS,
  analyzeDiscoveryPackSemantics,
  discoverSources,
  parseYamlOrJson,
  splitSourcePatterns,
  toRelativePath,
} from './lib.mjs';

const DEFAULT_SCHEMA_PATH = 'schema/discovery-pack-v1.schema.json';
const DEFAULT_OUTPUT_DIR = 'artifacts/discovery-pack';
const DEFAULT_REPORT_JSON = 'discovery-pack-compile-report.json';
const DEFAULT_REPORT_MD = 'discovery-pack-compile-report.md';
const OUTPUT_FILE_BY_TARGET = {
  'plan-spec': 'plan-to-spec-normalized.md',
  'context-pack-scaffold': 'context-pack-scaffold.yaml',
};
const SUPPORTED_TARGETS = new Set(Object.keys(OUTPUT_FILE_BY_TARGET));
const SUPPORTED_STATUSES = new Set(['hypothesis', 'reviewed', 'approved', 'rejected', 'deferred']);

const escapeMarkdownTableCell = (value) =>
  String(value ?? '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/`/g, '\\`')
    .replace(/\|/g, '\\|')
    .replace(/\r?\n/g, '<br>');

const slugify = (value) =>
  String(value ?? '')
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '') || 'discovery-pack';

const toPascalFromId = (value, fallback = 'GeneratedMorphisms') => {
  const tokens = String(value ?? '')
    .trim()
    .split(/[^A-Za-z0-9]+/)
    .filter(Boolean)
    .filter((token) => !['buc', 'goal', 'req', 'flow', 'actor', 'ext', 'dec', 'asm', 'oq'].includes(token.toLowerCase()));
  if (tokens.length === 0) {
    return fallback;
  }
  return tokens.map((token) => token.charAt(0).toUpperCase() + token.slice(1).toLowerCase()).join('');
};

const uniqueStrings = (values) => Array.from(new Set(values.filter((value) => typeof value === 'string' && value.trim())));

const sectionEntries = (pack, section) => (Array.isArray(pack?.[section]) ? pack[section] : []);

const readRequiredValue = (argv, index, flag) => {
  const value = argv[index + 1];
  if (!value || value.startsWith('-')) {
    throw Object.assign(new Error(`missing value for ${flag}`), { exitCode: 2 });
  }
  return value;
};

function printHelp() {
  process.stdout.write(`Discovery Pack compiler\n\nUsage:\n  node scripts/discovery-pack/compile.mjs --target <plan-spec|context-pack-scaffold> [options]\n\nOptions:\n  --target <name>         plan-spec | context-pack-scaffold\n  --sources <glob>        Source glob (repeatable, comma-separated supported)\n  --schema <path>         JSON Schema path (default: ${DEFAULT_SCHEMA_PATH})\n  --output-dir <dir>      Output directory (default: ${DEFAULT_OUTPUT_DIR})\n  --include-status <s>    Repeatable, comma-separated supported (default: approved)\n  --help, -h              Show this help\n`);
}

export function parseArgs(argv) {
  const options = {
    target: '',
    sources: [],
    schemaPath: DEFAULT_SCHEMA_PATH,
    outputDir: DEFAULT_OUTPUT_DIR,
    includeStatuses: [],
    help: false,
  };

  const appendSources = (rawValue) => {
    for (const token of splitSourcePatterns(rawValue)) {
      const trimmed = token.trim();
      if (trimmed) {
        options.sources.push(trimmed);
      }
    }
  };

  const appendStatuses = (rawValue) => {
    for (const token of rawValue.split(',')) {
      const trimmed = token.trim();
      if (!trimmed) {
        continue;
      }
      if (!SUPPORTED_STATUSES.has(trimmed)) {
        throw Object.assign(new Error(`unsupported --include-status value: ${trimmed}`), { exitCode: 2 });
      }
      if (!options.includeStatuses.includes(trimmed)) {
        options.includeStatuses.push(trimmed);
      }
    }
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--target') {
      options.target = readRequiredValue(argv, index, '--target');
      index += 1;
      continue;
    }
    if (arg.startsWith('--target=')) {
      options.target = arg.slice('--target='.length);
      continue;
    }
    if (arg === '--sources') {
      appendSources(readRequiredValue(argv, index, '--sources'));
      index += 1;
      continue;
    }
    if (arg.startsWith('--sources=')) {
      appendSources(arg.slice('--sources='.length));
      continue;
    }
    if (arg === '--schema') {
      options.schemaPath = readRequiredValue(argv, index, '--schema');
      index += 1;
      continue;
    }
    if (arg.startsWith('--schema=')) {
      options.schemaPath = arg.slice('--schema='.length);
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = readRequiredValue(argv, index, '--output-dir');
      index += 1;
      continue;
    }
    if (arg.startsWith('--output-dir=')) {
      options.outputDir = arg.slice('--output-dir='.length);
      continue;
    }
    if (arg === '--include-status') {
      appendStatuses(readRequiredValue(argv, index, '--include-status'));
      index += 1;
      continue;
    }
    if (arg.startsWith('--include-status=')) {
      appendStatuses(arg.slice('--include-status='.length));
      continue;
    }
    throw Object.assign(new Error(`unknown option: ${arg}`), { exitCode: 2 });
  }

  if (options.help) {
    return options;
  }
  if (!SUPPORTED_TARGETS.has(options.target)) {
    throw Object.assign(new Error(`unsupported --target value: ${options.target || '(missing)'}`), { exitCode: 2 });
  }
  if (options.includeStatuses.length === 0) {
    options.includeStatuses = ['approved'];
  }
  if (options.sources.length === 0) {
    options.sources = [...DEFAULT_SOURCES];
  }
  return options;
}

const loadSchema = (schemaPath) => {
  const resolvedSchema = path.resolve(schemaPath);
  const schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
  return { schema, resolvedSchema };
};

const selectByStatus = (pack, includeStatuses) => {
  const included = new Set(includeStatuses);
  const selected = {};
  const excluded = {};
  for (const section of DISCOVERY_PACK_SECTIONS) {
    selected[section] = [];
    excluded[section] = [];
    for (const entry of sectionEntries(pack, section)) {
      const status = typeof entry?.status === 'string' ? entry.status : '';
      if (included.has(status)) {
        selected[section].push(entry);
      } else {
        excluded[section].push({
          id: typeof entry?.id === 'string' ? entry.id : '',
          status,
          reason: 'status-excluded',
        });
      }
    }
  }
  return { selected, excluded };
};

const buildActorLookup = (entriesBySection) => {
  const lookup = new Map();
  for (const section of ['actors', 'external_systems']) {
    for (const entry of entriesBySection[section] ?? []) {
      const id = typeof entry?.id === 'string' ? entry.id.trim() : '';
      if (id) {
        lookup.set(id, entry);
      }
    }
  }
  return lookup;
};

const buildGoalLookup = (entriesBySection) => {
  const lookup = new Map();
  for (const entry of entriesBySection.goals ?? []) {
    const id = typeof entry?.id === 'string' ? entry.id.trim() : '';
    if (id) {
      lookup.set(id, entry);
    }
  }
  return lookup;
};

const getSelectedEntryMaps = (entriesBySection) => {
  const selectedEntries = new Map();
  for (const section of DISCOVERY_PACK_SECTIONS) {
    for (const entry of entriesBySection[section] ?? []) {
      const id = typeof entry?.id === 'string' ? entry.id.trim() : '';
      if (id) {
        selectedEntries.set(id, entry);
      }
    }
  }
  return selectedEntries;
};

const collectTracedStatements = (entry, selectedEntries) => {
  const traceIds = Array.isArray(entry?.traces_to) ? entry.traces_to : [];
  const statements = [];
  for (const ref of traceIds) {
    const target = selectedEntries.get(ref);
    const statement = typeof target?.statement === 'string' && target.statement.trim()
      ? target.statement.trim()
      : typeof target?.title === 'string' && target.title.trim()
        ? target.title.trim()
        : '';
    if (statement) {
      statements.push(statement);
    }
  }
  return uniqueStrings(statements);
};

const buildAcceptanceCriterion = (entry, actorLookup, goalLookup, selectedEntries) => {
  const actorNames = uniqueStrings(
    (Array.isArray(entry?.actor_ids) ? entry.actor_ids : [])
      .map((id) => actorLookup.get(id))
      .map((actor) => actor?.title ?? actor?.id ?? ''),
  );
  const goalStatements = uniqueStrings(
    (Array.isArray(entry?.primary_goal_ids) ? entry.primary_goal_ids : [])
      .map((id) => goalLookup.get(id))
      .map((goal) => goal?.statement ?? goal?.title ?? ''),
  );
  const tracedStatements = collectTracedStatements(entry, selectedEntries);
  const whenText = typeof entry?.statement === 'string' && entry.statement.trim()
    ? entry.statement.trim().replace(/\.$/, '')
    : typeof entry?.title === 'string' && entry.title.trim()
      ? entry.title.trim().replace(/\.$/, '')
      : 'the discovered business flow is executed';
  const thenText = tracedStatements[0] ?? goalStatements[0] ?? whenText;
  const actorText = actorNames.join(' and ') || 'the relevant actor';
  return `Given ${actorText} is operating within the approved workflow When ${whenText} Then ${thenText}.`;
};

const formatList = (items, formatter, empty = '- none captured') => {
  if (!items || items.length === 0) {
    return [empty];
  }
  return items.map(formatter);
};

const buildPlanSpecMarkdown = (pack, selection, compileMeta) => {
  const actorLookup = buildActorLookup(selection.selected);
  const goalLookup = buildGoalLookup(selection.selected);
  const selectedEntries = getSelectedEntryMaps(selection.selected);
  const selectedGoals = selection.selected.goals;
  const selectedRequirements = selection.selected.requirements;
  const selectedUseCases = selection.selected.business_use_cases;
  const selectedDecisions = selection.selected.decisions;
  const selectedAssumptions = selection.selected.assumptions;
  const selectedOpenQuestions = selection.selected.open_questions;

  const lines = [
    '# Discovery Pack -> Plan Spec (Generated)',
    '',
    '> Non-authoritative artifact generated from Discovery Pack. Review and edit before promoting anything to repo SSOT.',
    '',
    '## 0. Metadata / メタデータ',
    '',
    `- Source file: \`${compileMeta.sourceFile}\``,
    `- Profile: ${pack.profile ?? 'unknown'}`,
    `- Generated at (UTC): ${compileMeta.generatedAt}`,
    `- Target: ${compileMeta.target}`,
    `- Included statuses: ${compileMeta.includeStatuses.join(', ')}`,
    '',
    '## 1. Goal and Scope / 目的とスコープ',
    '',
    '- Business goal:',
    ...formatList(
      selectedGoals,
      (goal) => `  - ${goal.id}: ${(goal.statement ?? goal.title ?? '').trim() || goal.id}`,
    ),
    '- In scope:',
    ...formatList(
      [...selectedRequirements, ...selectedUseCases],
      (entry) => `  - ${entry.id}: ${(entry.statement ?? entry.title ?? '').trim() || entry.id}`,
    ),
    '- Out of scope:',
    '  - See compile report for status-excluded discovery elements and unresolved questions.',
    '- Success criteria (high level):',
    ...formatList(
      selectedGoals,
      (goal) => `  - ${goal.title ?? goal.id}`,
    ),
    '',
    '## 2. Requirements Snapshot / 要件スナップショット',
    '',
    '- Functional requirements (FR):',
    ...formatList(
      selectedRequirements,
      (entry, index) => `  - FR-${index + 1}: ${(entry.statement ?? entry.title ?? '').trim() || entry.id}`,
    ),
    '- Constraints / Decisions:',
    ...formatList(
      selectedDecisions,
      (entry) => `  - ${entry.id}: ${(entry.statement ?? entry.title ?? '').trim() || entry.id}${entry.outcome ? ` (outcome: ${entry.outcome})` : ''}`,
    ),
    '- Assumptions:',
    ...formatList(
      selectedAssumptions,
      (entry) => `  - ${entry.id}: ${(entry.statement ?? entry.title ?? '').trim() || entry.id}`,
    ),
    '',
    '## 3. Acceptance Criteria (AC) / 受入基準',
    '',
  ];

  const acceptanceSource = selectedUseCases.length > 0
    ? selectedUseCases.map((entry) => ({
        id: entry.id,
        criterion: buildAcceptanceCriterion(entry, actorLookup, goalLookup, selectedEntries),
      }))
    : selectedRequirements.map((entry) => ({
        id: entry.id,
        criterion: `${(entry.statement ?? entry.title ?? '').trim() || entry.id}`,
      }));

  if (acceptanceSource.length === 0) {
    lines.push('- AC-1: TODO: define acceptance criteria from approved discovery elements');
  } else {
    acceptanceSource.forEach((entry, index) => {
      lines.push(`- AC-${index + 1}: ${entry.criterion}`);
    });
  }

  lines.push(
    '',
    '## 4. Open Questions / 未解決論点',
    '',
    ...formatList(
      selectedOpenQuestions,
      (entry) => `- ${entry.id}: ${(entry.question ?? entry.title ?? '').trim() || entry.id}${entry.blocking === true ? ' [blocking]' : ' [non-blocking]'}`,
      '- none selected by current compile status filter',
    ),
    '',
    '## 5. Discovery References / 参照元メモ',
    '',
    '- Reviewed source refs used by this artifact:',
    ...formatList(
      pack.sources ?? [],
      (source) => `  - ${source.id}: ${source.title ?? source.path ?? source.uri ?? source.id}`,
      '  - none captured',
    ),
    '',
    '## 6. Review Notes / レビュー観点',
    '',
    '- This file is intended to be fed into `ae tests:scaffold --input ...` after human review when the acceptance criteria look appropriate.',
    '- Status-excluded discovery elements remain in the compile report and are not silently promoted.',
    '- Context Pack remains the design SSOT; this document is a normalization artifact only.',
  );

  return `${lines.join('\n').trimEnd()}\n`;
};

const buildGlossaryTerms = (entries) => {
  const terms = [];
  const seen = new Set();
  for (const entry of entries) {
    const title = typeof entry?.title === 'string' && entry.title.trim() ? entry.title.trim() : '';
    if (!title) {
      continue;
    }
    const term = slugify(title).replace(/-/g, '_');
    if (seen.has(term)) {
      continue;
    }
    seen.add(term);
    terms.push({
      term,
      ja: title,
      note: `generated from discovery entry ${entry.id}`,
    });
  }
  return terms;
};

const buildContextPackScaffold = (pack, selection, compileMeta) => {
  const selectedEntries = getSelectedEntryMaps(selection.selected);
  const goalLookup = buildGoalLookup(selection.selected);
  const selectedGoals = selection.selected.goals;
  const selectedRequirements = selection.selected.requirements;
  const selectedUseCases = selection.selected.business_use_cases;
  const selectedFlows = selection.selected.flows;
  const selectedDecisions = selection.selected.decisions;
  const selectedOpenQuestions = selection.selected.open_questions;

  const scaffold = {
    version: 1,
    name: `${slugify(selectedUseCases[0]?.title ?? selectedGoals[0]?.title ?? pack.profile ?? 'discovery-pack')}-context-pack-scaffold`,
    generated_from: {
      discovery_pack: {
        source_file: compileMeta.sourceFile,
        profile: pack.profile ?? 'unknown',
        included_statuses: compileMeta.includeStatuses,
        compile_target: compileMeta.target,
      },
      selected_ids: {
        goals: selectedGoals.map((entry) => entry.id),
        requirements: selectedRequirements.map((entry) => entry.id),
        business_use_cases: selectedUseCases.map((entry) => entry.id),
        flows: selectedFlows.map((entry) => entry.id),
        decisions: selectedDecisions.map((entry) => entry.id),
        open_questions: selectedOpenQuestions.map((entry) => entry.id),
      },
    },
    generated_at: compileMeta.generatedAt,
    problem_statement: {
      goals: selectedGoals.map((entry) => (entry.statement ?? entry.title ?? '').trim() || entry.id),
      non_goals: [],
    },
    domain_glossary: {
      terms: buildGlossaryTerms([
        ...selection.selected.actors,
        ...selection.selected.external_systems,
      ]),
    },
    objects: [],
    morphisms: selectedUseCases.map((entry, index) => {
      const tracedStatements = collectTracedStatements(entry, selectedEntries);
      const primaryGoals = uniqueStrings(
        (Array.isArray(entry?.primary_goal_ids) ? entry.primary_goal_ids : [])
          .map((id) => goalLookup.get(id))
          .map((goal) => goal?.statement ?? goal?.title ?? ''),
      );
      return {
        id: toPascalFromId(entry.id, `GeneratedMorphism${index + 1}`),
        input: {},
        output: {},
        pre: tracedStatements.length > 0 ? tracedStatements : ['TODO: derive preconditions from approved discovery requirements'],
        post: primaryGoals.length > 0 ? primaryGoals : ['TODO: define expected state changes'],
        failures: ['TODO: define failure modes'],
      };
    }),
    diagrams: selectedFlows
      .filter((entry) => entry?.kind !== 'as-is')
      .map((entry, index) => ({
        id: entry.id || `D-${index + 1}`,
        statement: `Translate discovery flow \"${entry.title ?? entry.id}\" into a context-pack diagram statement.`,
        verification: ['manual-review'],
      })),
    constraints: {
      candidate_requirements: selectedRequirements.map((entry) => ({
        id: entry.id,
        statement: (entry.statement ?? entry.title ?? '').trim() || entry.id,
      })),
      approved_decisions: selectedDecisions.map((entry) => ({
        id: entry.id,
        statement: (entry.statement ?? entry.title ?? '').trim() || entry.id,
        outcome: entry.outcome ?? null,
      })),
      blocking_open_questions: selectedOpenQuestions
        .filter((entry) => entry.blocking === true)
        .map((entry) => ({
          id: entry.id,
          question: (entry.question ?? entry.title ?? '').trim() || entry.id,
        })),
    },
    acceptance_tests: selectedUseCases.map((entry, index) => ({
      id: `AT-${index + 1}`,
      scenario: (entry.statement ?? entry.title ?? '').trim() || entry.id,
      expected: (() => {
        const tracedStatements = collectTracedStatements(entry, selectedEntries);
        const goalStatements = uniqueStrings(
          (Array.isArray(entry?.primary_goal_ids) ? entry.primary_goal_ids : [])
            .map((id) => goalLookup.get(id))
            .map((goal) => goal?.statement ?? goal?.title ?? ''),
        );
        const expectedStatements = uniqueStrings([...tracedStatements, ...goalStatements]);
        return expectedStatements.length > 0 ? expectedStatements : ['TODO: define expected behavior'];
      })(),
    })),
    coding_conventions: {
      language: 'TBD',
      directory: [],
      dependencies: {},
    },
    forbidden_changes: [],
  };

  const yamlBody = yaml.stringify(scaffold, { indent: 2 });
  return `# Non-authoritative scaffold generated from Discovery Pack.\n# Review and edit before promoting to Context Pack SSOT.\n${yamlBody}`;
};

const buildMarkdownReport = (report) => {
  const lines = [
    '# Discovery Pack Compile Report',
    '',
    `- GeneratedAt: ${report.generatedAt}`,
    `- Status: ${report.status.toUpperCase()}`,
    `- Target: ${report.target}`,
    `- Source file: \`${report.sourceFile}\``,
    `- Included statuses: ${report.includeStatuses.join(', ')}`,
    `- Output artifact: \`${report.outputs.compiledArtifact}\``,
    '',
    '## Summary',
    `- selected elements: ${report.summary.selectedCount}`,
    `- excluded by status: ${report.summary.excludedByStatusCount}`,
    `- skipped by target rules: ${report.summary.skippedByTargetCount}`,
    `- unresolved refs: ${report.summary.unresolvedRefs}`,
    `- orphan warnings: ${report.summary.orphanWarnings}`,
    `- blocking open questions: ${report.summary.blockingOpenQuestions}`,
    '',
    '## Section Counts',
    '',
    '| Section | Selected | Excluded by status |',
    '| --- | --- | --- |',
  ];

  for (const section of DISCOVERY_PACK_SECTIONS) {
    lines.push(`| ${escapeMarkdownTableCell(section)} | ${report.summary.selectedBySection[section] ?? 0} | ${report.summary.excludedBySection[section] ?? 0} |`);
  }

  lines.push('', '## Target-specific skips', '', '| ID | Section | Reason |', '| --- | --- | --- |');
  if (report.targetSkips.length === 0) {
    lines.push('| none | - | - |');
  } else {
    for (const skip of report.targetSkips) {
      lines.push(`| ${escapeMarkdownTableCell(skip.id)} | ${escapeMarkdownTableCell(skip.section)} | ${escapeMarkdownTableCell(skip.reason)} |`);
    }
  }

  const violations = [...report.errors, ...report.warnings];
  lines.push('', '## Validation notes', '', '| Severity | Type | ID | Message |', '| --- | --- | --- | --- |');
  if (violations.length === 0) {
    lines.push('| info | none | - | No validation notes |');
  } else {
    for (const item of violations) {
      lines.push(`| ${escapeMarkdownTableCell(item.severity)} | ${escapeMarkdownTableCell(item.type)} | ${escapeMarkdownTableCell(item.id ?? '')} | ${escapeMarkdownTableCell(item.message)} |`);
    }
  }

  return `${lines.join('\n')}\n`;
};

const writeOutputs = (report, compiledContent, options) => {
  const outputDir = path.resolve(options.outputDir);
  fs.mkdirSync(outputDir, { recursive: true });
  const compiledArtifactPath = path.join(outputDir, OUTPUT_FILE_BY_TARGET[options.target]);
  const reportJsonPath = path.join(outputDir, DEFAULT_REPORT_JSON);
  const reportMarkdownPath = path.join(outputDir, DEFAULT_REPORT_MD);
  report.outputs = {
    compiledArtifact: compiledContent ? toRelativePath(compiledArtifactPath) : null,
    reportJson: toRelativePath(reportJsonPath),
    reportMarkdown: toRelativePath(reportMarkdownPath),
  };
  if (compiledContent) {
    fs.writeFileSync(compiledArtifactPath, compiledContent, 'utf8');
  }
  fs.writeFileSync(reportJsonPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
  fs.writeFileSync(reportMarkdownPath, buildMarkdownReport(report), 'utf8');
  return {
    compiledArtifactPath,
    reportJsonPath,
    reportMarkdownPath,
  };
};

const computeTargetSkips = (selection, target) => {
  if (target !== 'context-pack-scaffold') {
    return [];
  }
  const skips = [];
  for (const flow of selection.selected.flows) {
    if (flow?.kind === 'as-is') {
      skips.push({
        id: flow.id,
        section: 'flows',
        reason: 'as-is flows are not copied into context-pack diagrams',
      });
    }
  }
  return skips;
};

export function compileDiscoveryPack(options) {
  const { schema, resolvedSchema } = loadSchema(options.schemaPath);
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const sourceFiles = discoverSources(options.sources);

  if (sourceFiles.length === 0) {
    process.stderr.write(`[discovery-pack] no discovery-pack files matched source patterns: ${options.sources.join(', ')}\n`);
    return 2;
  }
  if (sourceFiles.length !== 1) {
    process.stderr.write(`[discovery-pack] compile expects exactly one discovery-pack input, matched ${sourceFiles.length}: ${sourceFiles.map((file) => toRelativePath(file)).join(', ')}\n`);
    return 2;
  }

  const sourceFile = sourceFiles[0];
  const relativeSourceFile = toRelativePath(sourceFile);
  let payload;
  try {
    payload = parseYamlOrJson(sourceFile);
  } catch (error) {
    process.stderr.write(`[discovery-pack] failed to parse ${relativeSourceFile}: ${error instanceof Error ? error.message : String(error)}\n`);
    return 1;
  }

  const errors = [];
  const warnings = [];

  if (!validate(payload)) {
    for (const validationError of validate.errors ?? []) {
      errors.push({
        severity: 'error',
        type: 'schema',
        id: validationError.instancePath || '/',
        message: validationError.message ?? 'schema validation failed',
      });
    }
  }

  const semantics = analyzeDiscoveryPackSemantics(payload, { strictApproved: false });
  for (const item of semantics.errors) {
    errors.push({ ...item, severity: 'error' });
  }
  for (const item of semantics.warnings) {
    warnings.push({ ...item, severity: 'warning' });
  }

  const selection = selectByStatus(payload, options.includeStatuses);
  const targetSkips = computeTargetSkips(selection, options.target);
  const generatedAt = new Date().toISOString();

  const report = {
    schemaVersion: 'discovery-pack-compile-report/v1',
    contractId: 'discovery-pack-compile-report.v1',
    generatedAt,
    status: 'pass',
    target: options.target,
    sourcePatterns: options.sources,
    sourceFile: relativeSourceFile,
    schemaPath: toRelativePath(resolvedSchema),
    includeStatuses: options.includeStatuses,
    profile: payload.profile ?? 'unknown',
    outputs: {
      compiledArtifact: '',
      reportJson: '',
      reportMarkdown: '',
    },
    summary: {
      selectedCount: DISCOVERY_PACK_SECTIONS.reduce((sum, section) => sum + selection.selected[section].length, 0),
      excludedByStatusCount: DISCOVERY_PACK_SECTIONS.reduce((sum, section) => sum + selection.excluded[section].length, 0),
      skippedByTargetCount: targetSkips.length,
      unresolvedRefs: semantics.summary.unresolvedSourceRefs + semantics.summary.unresolvedTraceRefs,
      orphanWarnings: semantics.summary.orphanApprovedRequirements + semantics.summary.orphanApprovedBusinessUseCases,
      blockingOpenQuestions: semantics.summary.blockingOpenQuestions,
      selectedBySection: Object.fromEntries(DISCOVERY_PACK_SECTIONS.map((section) => [section, selection.selected[section].length])),
      excludedBySection: Object.fromEntries(DISCOVERY_PACK_SECTIONS.map((section) => [section, selection.excluded[section].length])),
    },
    selectedIds: Object.fromEntries(DISCOVERY_PACK_SECTIONS.map((section) => [section, selection.selected[section].map((entry) => entry.id)])),
    excludedIds: Object.fromEntries(DISCOVERY_PACK_SECTIONS.map((section) => [section, selection.excluded[section]])),
    targetSkips,
    errors,
    warnings,
  };

  let compiledContent = '';
  if (errors.length === 0) {
    const compileMeta = {
      generatedAt,
      target: options.target,
      includeStatuses: options.includeStatuses,
      sourceFile: relativeSourceFile,
    };
    compiledContent = options.target === 'plan-spec'
      ? buildPlanSpecMarkdown(payload, selection, compileMeta)
      : buildContextPackScaffold(payload, selection, compileMeta);
  }

  report.status = errors.length > 0 ? 'fail' : warnings.length > 0 || targetSkips.length > 0 || report.summary.excludedByStatusCount > 0 ? 'warn' : 'pass';

  writeOutputs(report, compiledContent, options);

  process.stdout.write(`[discovery-pack] report(json): ${report.outputs.reportJson}\n`);
  process.stdout.write(`[discovery-pack] report(md): ${report.outputs.reportMarkdown}\n`);
  process.stdout.write(`[discovery-pack] compiled artifact: ${report.outputs.compiledArtifact}\n`);

  if (errors.length > 0) {
    process.stderr.write(`[discovery-pack] compile failed (${errors.length} error(s))\n`);
    return 1;
  }
  process.stdout.write(`[discovery-pack] compile completed (${report.summary.selectedCount} selected element(s), ${report.summary.excludedByStatusCount} excluded by status)\n`);
  return 0;
}

const run = () => {
  try {
    const options = parseArgs(process.argv);
    if (options.help) {
      printHelp();
      return 0;
    }
    return compileDiscoveryPack(options);
  } catch (error) {
    if (error instanceof Error) {
      process.stderr.write(`[discovery-pack] ${error.message}\n`);
    } else {
      process.stderr.write(`[discovery-pack] ${String(error)}\n`);
    }
    return error && typeof error === 'object' && 'exitCode' in error ? error.exitCode : 1;
  }
};

process.exitCode = run();
