#!/usr/bin/env node
import { existsSync, lstatSync, mkdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const SCRIPT_NAME = 'scripts/loop/run-report-only.mjs';
const INPUT_SCHEMA_PATH = 'schema/loop-run-input.schema.json';
const SUMMARY_SCHEMA_PATH = 'schema/loop-run-summary.schema.json';
const DEFAULT_INPUT = 'examples/loop-engineering/success/loop-input.json';
const DEFAULT_OUTPUT_JSON = 'artifacts/loop/loop-run-summary.json';
const DEFAULT_OUTPUT_MD = 'artifacts/loop/loop-run-summary.md';
const STOP_REASONS = new Set(['success', 'blocked', 'max-iterations', 'validation-failed', 'unsafe-action', 'human-required']);
const DECISION_TO_STOP_REASON = new Map([
  ['success', 'success'],
  ['blocked', 'blocked'],
  ['validation-failed', 'validation-failed'],
  ['unsafe-action', 'unsafe-action'],
  ['human-required', 'human-required'],
]);
const BUILT_IN_FORBIDDEN_ACTIONS = [
  'approve-pr',
  'approve-review',
  'bypass-review',
  'delete-branch',
  'dismiss-review',
  'hosted-llm-call',
  'merge-pr',
  'push-commit',
  'review-bypass',
  'submit-approval',
];

function toPosix(value) {
  return value.split(path.sep).join('/');
}

function normalizePathForReport(filePath, root = process.cwd()) {
  const resolved = path.resolve(filePath);
  const relative = path.relative(path.resolve(root), resolved);
  if (relative === '') return '.';
  return toPosix(relative && !relative.startsWith('..') ? relative : resolved);
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

function assertContainedInputPath(filePath, label, rootDir = process.cwd()) {
  const root = path.resolve(rootDir);
  const resolved = path.resolve(root, filePath);
  if (!isPathWithin(root, resolved)) {
    throw new Error(`${label} must stay within the working directory: ${filePath}`);
  }
  const stat = lstatIfExists(resolved);
  if (!stat) throw new Error(`${label} not found: ${filePath}`);
  if (stat.isSymbolicLink()) {
    throw new Error(`${label} must not be a symbolic link: ${filePath}`);
  }
  const realRoot = realpathSync.native(root);
  const realResolved = realpathSync.native(resolved);
  if (!isPathWithin(realRoot, realResolved)) {
    throw new Error(`${label} resolves outside the working directory: ${filePath}`);
  }
  return resolved;
}

function assertContainedReferencePath(filePath, label, rootDir = process.cwd()) {
  if (typeof filePath !== 'string' || filePath.trim() === '') {
    throw new Error(`${label} must be a non-empty path`);
  }
  const root = path.resolve(rootDir);
  const resolved = path.resolve(root, filePath);
  if (!isPathWithin(root, resolved)) {
    throw new Error(`${label} must stay within the working directory: ${filePath}`);
  }

  const realRoot = realpathSync.native(root);
  const existingAncestor = nearestExistingAncestor(resolved);
  if (!existingAncestor) {
    throw new Error(`${label} has no existing ancestor under the working directory: ${filePath}`);
  }
  const realAncestor = realpathIfExists(existingAncestor);
  if (!realAncestor || !isPathWithin(realRoot, realAncestor)) {
    throw new Error(`${label} resolves outside the working directory: ${filePath}`);
  }

  const stat = lstatIfExists(resolved);
  const realResolved = realpathIfExists(resolved);
  if (stat?.isSymbolicLink() && !realResolved) {
    throw new Error(`${label} must not be a broken symbolic link: ${filePath}`);
  }
  if (realResolved && !isPathWithin(realRoot, realResolved)) {
    throw new Error(`${label} resolves outside the working directory: ${filePath}`);
  }
  return resolved;
}

function normalizeReferencePathForReport(filePath, label) {
  return normalizePathForReport(assertContainedReferencePath(filePath, label));
}

function ensureContainedOutputPath(filePath, label, rootDir = process.cwd()) {
  const root = path.resolve(rootDir);
  const resolved = path.resolve(root, filePath);
  if (!isPathWithin(root, resolved)) {
    throw new Error(`${label} must stay within the working directory: ${filePath}`);
  }

  const realRoot = realpathSync.native(root);
  const outputStat = lstatIfExists(resolved);
  if (outputStat?.isSymbolicLink()) {
    throw new Error(`${label} must not be a symbolic link: ${filePath}`);
  }
  const resolvedOutput = realpathIfExists(resolved);
  if (resolvedOutput && !isPathWithin(realRoot, resolvedOutput)) {
    throw new Error(`${label} resolves outside the working directory: ${filePath}`);
  }

  const outputDir = path.dirname(resolved);
  const existingAncestor = nearestExistingAncestor(outputDir);
  if (!existingAncestor) {
    throw new Error(`${label} has no existing ancestor under the working directory: ${filePath}`);
  }
  const realAncestor = realpathIfExists(existingAncestor);
  if (!realAncestor || !isPathWithin(realRoot, realAncestor)) {
    throw new Error(`${label} output directory resolves outside the working directory: ${filePath}`);
  }

  mkdirSync(outputDir, { recursive: true });
  const realOutputDir = realpathSync.native(outputDir);
  if (!isPathWithin(realRoot, realOutputDir)) {
    throw new Error(`${label} output directory resolves outside the working directory: ${filePath}`);
  }
  const outputStatAfterMkdir = lstatIfExists(resolved);
  if (outputStatAfterMkdir?.isSymbolicLink()) {
    throw new Error(`${label} must not be a symbolic link: ${filePath}`);
  }
  const resolvedOutputAfterMkdir = realpathIfExists(resolved);
  if (resolvedOutputAfterMkdir && !isPathWithin(realRoot, resolvedOutputAfterMkdir)) {
    throw new Error(`${label} resolves outside the working directory: ${filePath}`);
  }
  return resolved;
}

function parseArgs(argv = process.argv) {
  const options = {
    input: DEFAULT_INPUT,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    generatedAt: null,
    maxIterations: null,
    noWrite: false,
    help: false,
  };
  const args = argv.slice(2);
  for (let index = 0; index < args.length; index += 1) {
    const arg = args[index];
    if (arg === '--' && index === 0) continue;
    if (arg === '--') break;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--no-write') {
      options.noWrite = true;
      continue;
    }
    const valueOptions = new Map([
      ['--input', 'input'],
      ['--output-json', 'outputJson'],
      ['--output-md', 'outputMd'],
      ['--generated-at', 'generatedAt'],
      ['--max-iterations', 'maxIterations'],
    ]);
    if (valueOptions.has(arg)) {
      const target = valueOptions.get(arg);
      const next = args[index + 1];
      if (!next || next.startsWith('--')) throw new Error(`${arg} requires a value`);
      options[target] = target === 'maxIterations' ? Number.parseInt(next, 10) : next;
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }
  if (options.maxIterations !== null && (!Number.isInteger(options.maxIterations) || options.maxIterations < 1)) {
    throw new Error('--max-iterations must be a positive integer');
  }
  return options;
}

function renderHelp() {
  return [
    'Report-only loop engineering fixture runner',
    '',
    'Usage:',
    `  node ${SCRIPT_NAME} [options]`,
    '',
    'Options:',
    `  --input <path>             loop input fixture (default: ${DEFAULT_INPUT})`,
    `  --output-json <path>       loop-run summary JSON (default: ${DEFAULT_OUTPUT_JSON})`,
    `  --output-md <path>         loop-run summary Markdown (default: ${DEFAULT_OUTPUT_MD})`,
    '  --generated-at <iso-date>  deterministic timestamp for fixtures/tests',
    '  --max-iterations <n>       override input maxIterations',
    '  --no-write                 build in memory without writing outputs',
    '  --help                     show this help',
  ].join('\n');
}

function readJson(filePath, label) {
  const resolved = path.resolve(filePath);
  if (!existsSync(resolved)) throw new Error(`${label} not found: ${filePath}`);
  return JSON.parse(readFileSync(resolved, 'utf8'));
}

function createSchemaValidator(schemaPath, label) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const schema = readJson(path.resolve(schemaPath), label);
  return ajv.compile(schema);
}

function formatSchemaErrors(errors) {
  return (errors || [])
    .map((error) => `${error.instancePath || '/'} ${error.message}`)
    .join('; ');
}

function assertSchemaValid(payload, schemaPath, label) {
  const validate = createSchemaValidator(schemaPath, `${label} schema`);
  if (!validate(payload)) {
    throw new Error(`${label} schema validation failed: ${formatSchemaErrors(validate.errors)}`);
  }
}

function assertLoopInput(input) {
  if (!input || typeof input !== 'object') throw new Error('loop input must be an object');
  if (input.schemaVersion !== 'loop-run-input/v1') throw new Error('loop input schemaVersion must be loop-run-input/v1');
  if (input.reportOnly !== true) throw new Error('loop input must be reportOnly=true for this MVP');
  if (!input.goal?.issueRef || !input.goal?.summary) throw new Error('loop input goal.issueRef and goal.summary are required');
  if (!input.execPlan?.planId || !input.execPlan?.path) throw new Error('loop input execPlan.planId and execPlan.path are required');
  if (!Array.isArray(input.iterations) || input.iterations.length === 0) throw new Error('loop input requires at least one fixture iteration');
}

function forbiddenActions(input) {
  const forbidden = new Set([
    ...BUILT_IN_FORBIDDEN_ACTIONS,
    ...(input.safety?.forbiddenActions || []),
  ]);
  const detected = [];
  if (input.safety?.autoMergeAllowed === true) detected.push('auto-merge-enabled');
  if (input.safety?.hostedLlmCallsAllowed === true) detected.push('hosted-llm-enabled');
  for (const iteration of input.iterations || []) {
    const actionKind = String(iteration.actionHook?.kind || '').trim();
    if (forbidden.has(actionKind)) detected.push(actionKind);
    if (iteration.actionHook?.mutatesRepository === true && input.safety?.mutationsAllowed !== true) {
      detected.push(`${iteration.id}:mutates-repository`);
    }
  }
  return [...new Set(detected)].sort();
}

function normalizeFinding(finding) {
  return {
    severity: finding?.severity || 'info',
    code: finding?.code || 'loop-finding',
    message: finding?.message || 'Loop finding recorded by fixture.',
  };
}

function normalizeEvidence(evidence, label = 'observedEvidence.path') {
  return {
    id: evidence?.id || 'evidence.unknown',
    path: normalizeReferencePathForReport(evidence?.path || 'not_collected', label),
    status: evidence?.status || 'not_collected',
    summary: evidence?.summary || 'Evidence summary not provided.',
  };
}

function normalizeIteration(iteration, index) {
  const validation = iteration.validation || {};
  const findings = Array.isArray(iteration.findings) ? iteration.findings.map(normalizeFinding) : [];
  return {
    index,
    id: iteration.id || `iteration-${index}`,
    phase: iteration.phase || 'verify',
    plannedAction: iteration.plannedAction || 'Observe fixture and run validation command.',
    actionHook: {
      kind: iteration.actionHook?.kind || 'fixture-observation',
      description: iteration.actionHook?.description || 'Fixture action hook; no repository mutation.',
      mutatesRepository: Boolean(iteration.actionHook?.mutatesRepository),
    },
    validation: {
      command: validation.command || 'not-run',
      expectedStatus: validation.expectedStatus || 'pass',
      actualStatus: validation.actualStatus || 'not-run',
      ...(validation.rawOutputPath ? { rawOutputPath: normalizeReferencePathForReport(validation.rawOutputPath, `${iteration.id || `iteration-${index}`}.validation.rawOutputPath`) } : {}),
    },
    observedEvidence: Array.isArray(iteration.observedEvidence) && iteration.observedEvidence.length > 0
      ? iteration.observedEvidence.map((evidence, evidenceIndex) => normalizeEvidence(evidence, `${iteration.id || `iteration-${index}`}.observedEvidence[${evidenceIndex}].path`))
      : [normalizeEvidence(null, `${iteration.id || `iteration-${index}`}.observedEvidence[0].path`)],
    findings,
    decision: iteration.decision || 'continue',
    nextRecommendedAction: iteration.nextRecommendedAction || 'Continue to the next loop iteration.',
  };
}

function buildReviewBody(summary) {
  const lines = [
    `Result: ${summary.result}`,
    `Stop reason: ${summary.stopReason}`,
    `Iterations: ${summary.summary.iterationCount}`,
    `Next action: ${summary.nextRecommendedAction}`,
  ];
  if (summary.findings.length > 0) {
    lines.push('Findings:');
    for (const finding of summary.findings.slice(0, 5)) {
      lines.push(`- [${finding.severity}] ${finding.code}: ${finding.message}`);
    }
  }
  return lines.join('\n');
}

function buildLoopRun(options = parseArgs()) {
  const inputPath = assertContainedInputPath(options.input, 'loop input');
  const input = readJson(inputPath, 'loop input');
  assertSchemaValid(input, INPUT_SCHEMA_PATH, 'loop input');
  assertLoopInput(input);

  const generatedAt = options.generatedAt || new Date().toISOString();
  const maxIterations = options.maxIterations || input.maxIterations || input.iterations.length;
  const detectedForbidden = forbiddenActions(input);
  const iterations = [];
  const allFindings = [];
  let stopReason = null;
  let nextRecommendedAction = 'Review the loop-run summary and decide the next operator action.';

  if (detectedForbidden.length > 0) {
    stopReason = 'unsafe-action';
    allFindings.push({ severity: 'error', code: 'unsafe-action', message: `Forbidden action(s) detected: ${detectedForbidden.join(', ')}` });
    nextRecommendedAction = 'Stop the loop and ask a human to remove or approve the unsafe action explicitly.';
  }

  if (!stopReason) {
    for (const fixtureIteration of input.iterations.slice(0, maxIterations)) {
      const iteration = normalizeIteration(fixtureIteration, iterations.length + 1);
      iterations.push(iteration);
      allFindings.push(...iteration.findings);
      const validationMismatch = iteration.validation.expectedStatus !== iteration.validation.actualStatus;
      if (validationMismatch && (iteration.decision === 'continue' || iteration.decision === 'success')) {
        stopReason = 'validation-failed';
        allFindings.push({ severity: 'error', code: 'validation-status-mismatch', message: `${iteration.id} expected ${iteration.validation.expectedStatus} but observed ${iteration.validation.actualStatus}.` });
        nextRecommendedAction = 'Inspect validation output and update the plan before continuing.';
        break;
      }
      const mappedStopReason = DECISION_TO_STOP_REASON.get(iteration.decision);
      if (mappedStopReason) {
        stopReason = mappedStopReason;
        nextRecommendedAction = iteration.nextRecommendedAction;
        break;
      }
    }
  }

  if (!stopReason) {
    const reachedMaxIterations = iterations.length >= maxIterations;
    if (reachedMaxIterations) {
      stopReason = 'max-iterations';
      nextRecommendedAction = 'Stop after reaching max iterations; review whether another run should be scheduled.';
    } else {
      stopReason = 'blocked';
      allFindings.push({
        severity: 'warning',
        code: 'fixture-exhausted',
        message: `Loop fixture ended after ${iterations.length} iteration(s) before reaching maxIterations=${maxIterations}.`,
      });
      nextRecommendedAction = 'Add another fixture iteration or ask a human operator to decide whether the loop should continue.';
    }
  }

  const commands = [...new Set(iterations.map((iteration) => iteration.validation.command).filter((command) => command && command !== 'not-run'))];
  const result = STOP_REASONS.has(stopReason) ? stopReason : 'blocked';
  const summary = {
    schemaVersion: 'loop-run-summary/v1',
    generatedAt,
    runId: input.runId || path.basename(path.dirname(inputPath)) || 'loop-run',
    result,
    reportOnly: true,
    input: {
      schemaVersion: input.schemaVersion,
      sourcePath: normalizePathForReport(inputPath),
      goal: {
        issueRef: input.goal.issueRef,
        summary: input.goal.summary,
      },
      execPlan: {
        planId: input.execPlan.planId,
        path: normalizeReferencePathForReport(input.execPlan.path, 'execPlan.path'),
      },
      contextPackRefs: Array.isArray(input.contextPackRefs)
        ? input.contextPackRefs.map((ref, index) => normalizeReferencePathForReport(ref, `contextPackRefs[${index}]`))
        : [],
      maxIterations,
    },
    safety: {
      worktreeMode: input.safety?.worktreeMode || 'fixture',
      mutationsAllowed: Boolean(input.safety?.mutationsAllowed),
      hostedLlmCallsAllowed: Boolean(input.safety?.hostedLlmCallsAllowed),
      autoMergeAllowed: Boolean(input.safety?.autoMergeAllowed),
      forbiddenActionsDetected: detectedForbidden,
    },
    summary: {
      iterationCount: iterations.length,
      commandCount: commands.length,
      findingCount: allFindings.length,
    },
    iterations,
    commands,
    findings: allFindings,
    stopReason,
    nextRecommendedAction,
    reviewSurface: {
      title: `Loop run ${input.runId || path.basename(path.dirname(inputPath))}: ${result}`,
      body: '',
    },
  };
  summary.reviewSurface.body = buildReviewBody(summary);
  assertSchemaValid(summary, SUMMARY_SCHEMA_PATH, 'loop summary');
  return summary;
}

function renderMarkdown(summary) {
  const lines = [
    `# Report-only Loop Run: ${summary.runId}`,
    '',
    `- Result: \`${summary.result}\``,
    `- Stop reason: \`${summary.stopReason}\``,
    `- Report-only: ${summary.reportOnly}`,
    `- Generated at: ${summary.generatedAt}`,
    `- Source: \`${summary.input.sourcePath}\``,
    `- Issue: ${summary.input.goal.issueRef}`,
    `- ExecPlan: \`${summary.input.execPlan.planId}\` (${summary.input.execPlan.path})`,
    `- Next recommended action: ${summary.nextRecommendedAction}`,
    '',
    '## Safety',
    '',
    `- Worktree mode: \`${summary.safety.worktreeMode}\``,
    `- Mutations allowed: ${summary.safety.mutationsAllowed}`,
    `- Hosted LLM calls allowed: ${summary.safety.hostedLlmCallsAllowed}`,
    `- Auto-merge allowed: ${summary.safety.autoMergeAllowed}`,
    `- Forbidden actions detected: ${summary.safety.forbiddenActionsDetected.length > 0 ? summary.safety.forbiddenActionsDetected.join(', ') : 'none'}`,
    '',
    '## Iterations',
    '',
  ];
  for (const iteration of summary.iterations) {
    lines.push(`### ${iteration.index}. ${iteration.id}`);
    lines.push('');
    lines.push(`- Planned action: ${iteration.plannedAction}`);
    lines.push(`- Action hook: ${iteration.actionHook.kind} — ${iteration.actionHook.description}`);
    lines.push(`- Validation: \`${iteration.validation.command}\` (${iteration.validation.actualStatus}; expected ${iteration.validation.expectedStatus})`);
    for (const evidence of iteration.observedEvidence) {
      lines.push(`- Evidence ${evidence.id}: \`${evidence.status}\` at \`${evidence.path}\` — ${evidence.summary}`);
    }
    if (iteration.findings.length > 0) {
      for (const finding of iteration.findings) {
        lines.push(`- Finding [${finding.severity}] ${finding.code}: ${finding.message}`);
      }
    }
    lines.push(`- Decision: \`${iteration.decision}\``);
    lines.push(`- Next: ${iteration.nextRecommendedAction}`);
    lines.push('');
  }
  lines.push('## Commands', '');
  if (summary.commands.length === 0) lines.push('- No validation commands recorded.');
  for (const command of summary.commands) lines.push(`- \`${command}\``);
  lines.push('', '## Review surface', '', '```text', summary.reviewSurface.body, '```');
  return `${lines.join('\n')}\n`;
}

function writeJson(filePath, value) {
  writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

function writeText(filePath, value) {
  writeFileSync(filePath, value, 'utf8');
}

function run(options = parseArgs()) {
  if (options.help) {
    process.stdout.write(`${renderHelp()}\n`);
    return { status: 0, summary: null };
  }
  const summary = buildLoopRun(options);
  const markdown = renderMarkdown(summary);
  if (!options.noWrite) {
    const outputJson = ensureContainedOutputPath(options.outputJson, 'output JSON');
    const outputMd = ensureContainedOutputPath(options.outputMd, 'output Markdown');
    writeJson(outputJson, summary);
    writeText(outputMd, markdown);
  }
  process.stdout.write(`[loop:run-report-only] ${summary.result}: ${options.input} -> ${options.outputJson}\n`);
  return { status: summary.result === 'validation-failed' || summary.result === 'unsafe-action' ? 1 : 0, summary, markdown };
}

function isDirectExecution() {
  return Boolean(process.argv[1]) && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href;
}

if (isDirectExecution()) {
  try {
    const { status } = run(parseArgs(process.argv));
    process.exit(status);
  } catch (error) {
    process.stderr.write(`[loop:run-report-only] ${error.message}\n`);
    process.exit(1);
  }
}

export {
  buildLoopRun,
  parseArgs,
  renderMarkdown,
  run,
};
