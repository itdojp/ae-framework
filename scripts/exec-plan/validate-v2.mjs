#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_INPUT_PATH = 'fixtures/exec-plan/baseline.exec-plan.v2.json';
const DEFAULT_SCHEMA_PATH = 'schema/exec-plan.v2.schema.json';
const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/plan/exec-plan-v2-validation.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/plan/exec-plan.v2.md';
const PASS = 'pass';
const FAIL = 'fail';

export function parseArgs(argv = process.argv) {
  const options = {
    inputPath: DEFAULT_INPUT_PATH,
    schemaPath: DEFAULT_SCHEMA_PATH,
    outputJsonPath: DEFAULT_OUTPUT_JSON_PATH,
    outputMarkdownPath: DEFAULT_OUTPUT_MD_PATH,
    writeOutputs: true,
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];
    const readValue = (name) => {
      if (!next || next.startsWith('-')) {
        throw new Error(`missing value for ${name}`);
      }
      index += 1;
      return next;
    };

    if (arg === '--' && index === 2) {
      continue;
    }
    if (arg === '--') {
      break;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--file' || arg === '--input') {
      options.inputPath = readValue(arg);
      continue;
    }
    if (arg.startsWith('--file=')) {
      options.inputPath = arg.slice('--file='.length);
      continue;
    }
    if (arg.startsWith('--input=')) {
      options.inputPath = arg.slice('--input='.length);
      continue;
    }
    if (arg === '--schema') {
      options.schemaPath = readValue('--schema');
      continue;
    }
    if (arg.startsWith('--schema=')) {
      options.schemaPath = arg.slice('--schema='.length);
      continue;
    }
    if (arg === '--output-json') {
      options.outputJsonPath = readValue('--output-json');
      continue;
    }
    if (arg.startsWith('--output-json=')) {
      options.outputJsonPath = arg.slice('--output-json='.length);
      continue;
    }
    if (arg === '--output-md') {
      options.outputMarkdownPath = readValue('--output-md');
      continue;
    }
    if (arg.startsWith('--output-md=')) {
      options.outputMarkdownPath = arg.slice('--output-md='.length);
      continue;
    }
    if (arg === '--no-write') {
      options.writeOutputs = false;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

export function printHelp() {
  process.stdout.write(
    'ExecPlan v2 validator and Markdown renderer\n\n'
      + 'Usage:\n'
      + '  node scripts/exec-plan/validate-v2.mjs [options]\n\n'
      + 'Options:\n'
      + `  --file, --input <path>        input ExecPlan v2 JSON (default: ${DEFAULT_INPUT_PATH})\n`
      + `  --schema <path>               schema path (default: ${DEFAULT_SCHEMA_PATH})\n`
      + `  --output-json <path>          validation report JSON (default: ${DEFAULT_OUTPUT_JSON_PATH})\n`
      + `  --output-md <path>            rendered Markdown when valid; failure report when invalid (default: ${DEFAULT_OUTPUT_MD_PATH})\n`
      + '  --no-write                    validate without writing outputs\n'
      + '  --help, -h                    show help\n',
  );
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(path.resolve(filePath)), { recursive: true });
}

function readJsonFile(filePath) {
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) {
    throw new Error(`file not found: ${resolved}`);
  }
  return JSON.parse(fs.readFileSync(resolved, 'utf8'));
}

function normalizeAjvErrors(errors) {
  return (errors || []).map((error) => {
    const instancePath = error.instancePath || '/';
    const keyword = error.keyword || 'unknown';
    const message = error.message || 'schema validation error';
    const expected = error.params && Object.keys(error.params).length > 0
      ? ` (${JSON.stringify(error.params)})`
      : '';
    return `${instancePath} [${keyword}] ${message}${expected}`;
  });
}

function duplicateIds(items, label) {
  const seen = new Set();
  const duplicates = new Set();
  for (const item of items || []) {
    const id = item?.id;
    if (!id) {
      continue;
    }
    if (seen.has(id)) {
      duplicates.add(`${label}: ${id}`);
    }
    seen.add(id);
  }
  return [...duplicates];
}

function requireKnownRefs({ refs, known, location, label }) {
  const errors = [];
  for (const ref of refs || []) {
    if (!known.has(ref)) {
      errors.push(`${location} references unknown ${label}: ${ref}`);
    }
  }
  return errors;
}

function commandReferenceErrors(command, knownArtifactIds, location) {
  if (!command) {
    return [];
  }
  return requireKnownRefs({
    refs: command.expectedArtifactRefs || [],
    known: knownArtifactIds,
    location: `${location}.expectedArtifactRefs`,
    label: 'output artifact id',
  });
}

export function runSemanticValidation(payload) {
  const errors = [];
  const warnings = [];
  const outputArtifacts = payload?.outputArtifacts || [];
  const evidenceRequirements = payload?.evidenceRequirements || [];
  const tasks = payload?.taskGraph?.nodes || [];
  const outputArtifactIds = new Set(outputArtifacts.map((item) => item.id).filter(Boolean));
  const evidenceIds = new Set(evidenceRequirements.map((item) => item.id).filter(Boolean));
  const taskIds = new Set(tasks.map((item) => item.id).filter(Boolean));

  errors.push(...duplicateIds(outputArtifacts, 'outputArtifacts.id').map((item) => `duplicate ${item}`));
  errors.push(...duplicateIds(evidenceRequirements, 'evidenceRequirements.id').map((item) => `duplicate ${item}`));
  errors.push(...duplicateIds(tasks, 'taskGraph.nodes.id').map((item) => `duplicate ${item}`));

  for (const [index, evidence] of evidenceRequirements.entries()) {
    const location = `evidenceRequirements[${index}] (${evidence?.id || 'unknown'})`;
    errors.push(...requireKnownRefs({
      refs: evidence?.outputArtifactRefs || [],
      known: outputArtifactIds,
      location: `${location}.outputArtifactRefs`,
      label: 'output artifact id',
    }));
  }

  for (const [index, task] of tasks.entries()) {
    const location = `taskGraph.nodes[${index}] (${task?.id || 'unknown'})`;
    errors.push(...requireKnownRefs({
      refs: task?.dependsOn || [],
      known: taskIds,
      location: `${location}.dependsOn`,
      label: 'task id',
    }));
    errors.push(...requireKnownRefs({
      refs: task?.evidenceRequirementRefs || [],
      known: evidenceIds,
      location: `${location}.evidenceRequirementRefs`,
      label: 'evidence requirement id',
    }));
    errors.push(...requireKnownRefs({
      refs: task?.outputArtifactRefs || [],
      known: outputArtifactIds,
      location: `${location}.outputArtifactRefs`,
      label: 'output artifact id',
    }));
    for (const [commandIndex, command] of (task?.commands || []).entries()) {
      errors.push(...commandReferenceErrors(command, outputArtifactIds, `${location}.commands[${commandIndex}] (${command?.id || 'unknown'})`));
    }
  }

  for (const [index, command] of (payload?.verificationProfile?.commands || []).entries()) {
    errors.push(...commandReferenceErrors(command, outputArtifactIds, `verificationProfile.commands[${index}] (${command?.id || 'unknown'})`));
  }
  for (const [index, command] of (payload?.rollbackPlan?.validationCommands || []).entries()) {
    errors.push(...commandReferenceErrors(command, outputArtifactIds, `rollbackPlan.validationCommands[${index}] (${command?.id || 'unknown'})`));
  }
  for (const [index, stopRule] of (payload?.stopRules || []).entries()) {
    const location = `stopRules[${index}] (${stopRule?.id || 'unknown'})`;
    errors.push(...requireKnownRefs({
      refs: stopRule?.evidenceRequirementRefs || [],
      known: evidenceIds,
      location: `${location}.evidenceRequirementRefs`,
      label: 'evidence requirement id',
    }));
  }

  const requiredChecks = new Set(payload?.verificationProfile?.requiredChecks || []);
  if (!requiredChecks.has('verify-lite')) {
    warnings.push('verificationProfile.requiredChecks does not include verify-lite');
  }
  if (!requiredChecks.has('policy-gate')) {
    warnings.push('verificationProfile.requiredChecks does not include policy-gate');
  }
  const risk = payload?.riskProfile;
  if (risk?.selected === 'risk:high') {
    if (risk.requiresHumanApproval !== true) {
      errors.push('riskProfile.selected=risk:high requires riskProfile.requiresHumanApproval=true');
    }
    if (!Number.isInteger(risk.minHumanApprovals) || risk.minHumanApprovals < 1) {
      errors.push('riskProfile.selected=risk:high requires riskProfile.minHumanApprovals >= 1');
    }
  }
  if (risk?.selected === 'risk:low' && risk.requiresHumanApproval === true) {
    warnings.push('riskProfile.selected=risk:low has requiresHumanApproval=true; confirm this is intentional');
  }

  return { errors, warnings };
}

function validateAgainstSchema(schema, payload) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const ok = validate(payload);
  return {
    ok,
    errors: normalizeAjvErrors(validate.errors || []),
  };
}

export function validateExecPlanV2Payload(payload, schema) {
  const schemaResult = validateAgainstSchema(schema, payload);
  const semanticResult = schemaResult.ok ? runSemanticValidation(payload) : { errors: [], warnings: [] };
  const errors = [...schemaResult.errors, ...semanticResult.errors];
  const warnings = errors.length === 0 ? semanticResult.warnings : [];
  const result = errors.length > 0 ? FAIL : PASS;
  return {
    schemaVersion: 'exec-plan-v2-validation/v1',
    result,
    planId: payload?.planId || null,
    contractId: payload?.contractId || null,
    lifecycle: payload?.lifecycle || null,
    schemaErrors: schemaResult.errors,
    semanticErrors: semanticResult.errors,
    warnings,
  };
}

function bulletList(items, fallback = '- none') {
  if (!Array.isArray(items) || items.length === 0) {
    return [fallback];
  }
  return items.map((item) => `- ${item}`);
}

function table(rows, headers) {
  const escape = (value) => String(value ?? '').replaceAll('|', '\\|').replaceAll('\n', '<br>');
  const lines = [
    `| ${headers.map(escape).join(' | ')} |`,
    `| ${headers.map(() => '---').join(' | ')} |`,
  ];
  for (const row of rows) {
    lines.push(`| ${headers.map((header) => escape(row[header])).join(' | ')} |`);
  }
  return lines;
}

export function renderExecPlanMarkdown(plan) {
  const lines = [
    `# ExecPlan v2: ${plan.title}`,
    '',
    `- planId: \`${plan.planId}\``,
    `- contractId: \`${plan.contractId}\``,
    `- lifecycle: \`${plan.lifecycle}\``,
    `- risk: \`${plan.riskProfile.selected}\` / assurance decision: \`${plan.riskProfile.assuranceDecision}\``,
    `- source issue: ${plan.metadata.sourceIssue?.url || plan.metadata.sourceIssue?.id || 'not recorded'}`,
    '',
    '## Intent',
    '',
    plan.intent.summary,
    '',
    `Objective: ${plan.intent.objective}`,
    '',
    '### Non-goals',
    '',
    ...bulletList(plan.intent.nonGoals),
    '',
    '## Scope',
    '',
    '### In scope',
    '',
    ...bulletList(plan.scope.inScope),
    '',
    '### Out of scope',
    '',
    ...bulletList(plan.scope.outOfScope),
    '',
    '### Target files',
    '',
    ...table(
      plan.scope.targetFiles.map((item) => ({ Path: `\`${item.path}\``, Change: item.changeType, Reason: item.reason })),
      ['Path', 'Change', 'Reason'],
    ),
    '',
    '## Context references',
    '',
    ...table(
      plan.context.contextPackRefs.map((item) => ({ Kind: item.kind, Ref: item.refId, Path: item.path ? `\`${item.path}\`` : '', Description: item.description || '' })),
      ['Kind', 'Ref', 'Path', 'Description'],
    ),
    '',
    '## Task graph',
    '',
    ...table(
      plan.taskGraph.nodes.map((node) => ({
        ID: `\`${node.id}\``,
        Kind: node.kind,
        Owner: node.owner,
        Status: node.status,
        DependsOn: (node.dependsOn || []).map((dep) => `\`${dep}\``).join(', ') || '-',
        Evidence: (node.evidenceRequirementRefs || []).map((ref) => `\`${ref}\``).join(', ') || '-',
      })),
      ['ID', 'Kind', 'Owner', 'Status', 'DependsOn', 'Evidence'],
    ),
    '',
    '## Verification profile',
    '',
    `- mode: \`${plan.verificationProfile.mode}\``,
    `- required checks: ${(plan.verificationProfile.requiredChecks || []).map((item) => `\`${item}\``).join(', ') || 'none'}`,
    `- optional checks: ${(plan.verificationProfile.optionalChecks || []).map((item) => `\`${item}\``).join(', ') || 'none'}`,
    '',
    ...table(
      plan.verificationProfile.commands.map((command) => ({
        ID: `\`${command.id}\``,
        When: command.when,
        Command: `\`${command.command}\``,
        Evidence: command.expectedArtifactRefs.map((ref) => `\`${ref}\``).join(', '),
        Purpose: command.purpose,
      })),
      ['ID', 'When', 'Command', 'Evidence', 'Purpose'],
    ),
    '',
    '## Evidence requirements',
    '',
    ...table(
      plan.evidenceRequirements.map((evidence) => ({
        ID: `\`${evidence.id}\``,
        Kind: evidence.kind,
        RequiredBefore: evidence.requiredBefore,
        Producer: evidence.producer,
        Artifacts: evidence.outputArtifactRefs.map((ref) => `\`${ref}\``).join(', '),
        Claims: (evidence.claimRefs || []).join(', ') || '-',
      })),
      ['ID', 'Kind', 'RequiredBefore', 'Producer', 'Artifacts', 'Claims'],
    ),
    '',
    '## Output artifacts',
    '',
    ...table(
      plan.outputArtifacts.map((artifact) => ({
        ID: `\`${artifact.id}\``,
        Path: `\`${artifact.path}\``,
        Contract: artifact.contractId,
        RequiredBefore: artifact.requiredBefore,
      })),
      ['ID', 'Path', 'Contract', 'RequiredBefore'],
    ),
    '',
    '## Stop rules',
    '',
    ...table(
      plan.stopRules.map((rule) => ({
        ID: `\`${rule.id}\``,
        Severity: rule.severity,
        Action: rule.action,
        Condition: rule.condition,
      })),
      ['ID', 'Severity', 'Action', 'Condition'],
    ),
    '',
    '## Rollback plan',
    '',
    plan.rollbackPlan.strategy,
    '',
    ...bulletList(plan.rollbackPlan.steps),
  ];
  return `${lines.join('\n')}\n`;
}

export function renderValidationMarkdown(report) {
  const lines = [
    '# ExecPlan v2 Validation',
    '',
    `- result: \`${report.result}\``,
    `- planId: ${report.planId ? `\`${report.planId}\`` : 'not available'}`,
    `- contractId: ${report.contractId ? `\`${report.contractId}\`` : 'not available'}`,
    '',
  ];
  if (report.schemaErrors.length > 0) {
    lines.push('## Schema errors', '', ...report.schemaErrors.map((item) => `- ${item}`), '');
  }
  if (report.semanticErrors.length > 0) {
    lines.push('## Semantic errors', '', ...report.semanticErrors.map((item) => `- ${item}`), '');
  }
  if (report.warnings.length > 0) {
    lines.push('## Warnings', '', ...report.warnings.map((item) => `- ${item}`), '');
  }
  if (report.schemaErrors.length === 0 && report.semanticErrors.length === 0 && report.warnings.length === 0) {
    lines.push('- no issues', '');
  }
  return `${lines.join('\n')}\n`;
}

export function validateExecPlanV2File(options = {}) {
  const normalizedOptions = {
    inputPath: DEFAULT_INPUT_PATH,
    schemaPath: DEFAULT_SCHEMA_PATH,
    ...(options || {}),
  };
  const payload = readJsonFile(normalizedOptions.inputPath);
  const schema = readJsonFile(normalizedOptions.schemaPath);
  const report = validateExecPlanV2Payload(payload, schema);
  const markdown = report.result === PASS ? renderExecPlanMarkdown(payload) : renderValidationMarkdown(report);
  return { payload, report, markdown };
}

export function main(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }

  const { report, markdown } = validateExecPlanV2File(options);
  const reportWithPaths = {
    ...report,
    inputPath: path.resolve(options.inputPath),
    schemaPath: path.resolve(options.schemaPath),
    outputMarkdownPath: options.writeOutputs ? path.resolve(options.outputMarkdownPath) : null,
  };

  if (options.writeOutputs) {
    ensureDirectory(options.outputJsonPath);
    fs.writeFileSync(path.resolve(options.outputJsonPath), `${JSON.stringify(reportWithPaths, null, 2)}\n`);
    ensureDirectory(options.outputMarkdownPath);
    fs.writeFileSync(path.resolve(options.outputMarkdownPath), markdown);
  }

  process.stdout.write(`Validated ${options.inputPath}: ${report.result}\n`);
  for (const error of [...report.schemaErrors, ...report.semanticErrors]) {
    process.stderr.write(`- ${error}\n`);
  }
  for (const warning of report.warnings) {
    process.stderr.write(`warning: ${warning}\n`);
  }
  return report.result === FAIL ? 1 : 0;
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  try {
    process.exit(main(process.argv));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`[exec-plan:v2:validate] ${message}\n`);
    process.exit(1);
  }
}
