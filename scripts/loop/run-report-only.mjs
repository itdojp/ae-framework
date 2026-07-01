#!/usr/bin/env node
import { existsSync, lstatSync, mkdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const SCRIPT_NAME = 'scripts/loop/run-report-only.mjs';
const INPUT_SCHEMA_PATH = 'schema/loop-run-input.schema.json';
const POLICY_SCHEMA_PATH = 'schema/loop-policy.schema.json';
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
const DEFAULT_LOOP_POLICY = Object.freeze({
  schemaVersion: 'loop-policy/v1',
  policyId: 'loop-report-only-default',
  reportOnly: true,
  budgets: {
    maxIterations: 10,
    wallClockBudgetSeconds: 1800,
    modifiedFileLimit: 0,
  },
  commandPolicy: {
    allowList: [],
    denyList: ['gh pr merge', 'git push', 'rm -rf', 'curl '],
  },
  pathPolicy: {
    allowedPrefixes: ['.'],
    deniedPrefixes: ['.git', '.env', 'node_modules'],
  },
  evidenceRequirements: {
    requiredEvidenceIds: [],
    missingEvidenceStops: true,
  },
  humanApproval: {
    requiredRiskLevels: ['high', 'critical'],
    approvalEvidenceIds: ['ev.human-approval'],
  },
  stopRules: {
    stopOnDeniedCommand: true,
    stopOnDeniedPath: true,
    stopOnMissingEvidence: true,
    stopOnHighRiskEscalation: true,
    repeatedFailureThreshold: 2,
  },
  privacy: {
    redactionMode: 'metadata-only',
    publicRawLogsAllowed: false,
    disallowedRawLogClasses: ['prompt', 'secret', 'token', 'raw-llm-output'],
  },
});

function toPosix(value) {
  return value.split(path.sep).join('/');
}

function stableJson(value) {
  if (Array.isArray(value)) return `[${value.map(stableJson).join(',')}]`;
  if (value && typeof value === 'object') {
    return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableJson(value[key])}`).join(',')}}`;
  }
  return JSON.stringify(value);
}

function sha256(value) {
  return createHash('sha256').update(value).digest('hex');
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
    policy: null,
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
      ['--policy', 'policy'],
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
    '  --policy <path>            loop-policy/v1 file; overrides input policyRef when provided',
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

function loadLoopPolicy(options, input) {
  const requestedPolicy = options.policy || input.policyRef || null;
  if (!requestedPolicy) {
    const policy = JSON.parse(JSON.stringify(DEFAULT_LOOP_POLICY));
    assertSchemaValid(policy, POLICY_SCHEMA_PATH, 'loop policy');
    return { policy, sourcePath: 'built-in' };
  }
  const policyPath = assertContainedInputPath(requestedPolicy, 'loop policy');
  const policy = readJson(policyPath, 'loop policy');
  assertSchemaValid(policy, POLICY_SCHEMA_PATH, 'loop policy');
  return { policy, sourcePath: normalizePathForReport(policyPath) };
}

function commandMatches(command, pattern, mode = 'deny') {
  const normalizedCommand = String(command || '').trim();
  const normalizedPattern = String(pattern || '').trim();
  if (!normalizedCommand || !normalizedPattern) return false;
  if (mode === 'allow') {
    return normalizedCommand === normalizedPattern || normalizedCommand.startsWith(`${normalizedPattern} `);
  }
  return normalizedCommand === normalizedPattern || normalizedCommand.startsWith(`${normalizedPattern} `) || normalizedCommand.includes(normalizedPattern);
}

function commandPolicyFinding(command, policy) {
  const allowList = policy.commandPolicy?.allowList || [];
  const denyList = policy.commandPolicy?.denyList || [];
  const deniedBy = denyList.find((pattern) => commandMatches(command, pattern, 'deny'));
  if (deniedBy) {
    return { severity: 'error', code: 'loop-policy-denied-command', message: `Validation command is denied by loop policy: ${deniedBy}` };
  }
  if (allowList.length > 0 && !allowList.some((pattern) => commandMatches(command, pattern, 'allow'))) {
    return { severity: 'error', code: 'loop-policy-command-not-allowed', message: 'Validation command is not included in the loop policy allow list.' };
  }
  return null;
}

function normalizePolicyPrefix(prefix) {
  const normalized = toPosix(String(prefix || '').trim()).replace(/^\.\//, '').replace(/\/$/, '');
  return normalized === '' ? '.' : normalized;
}

function pathMatchesPrefix(filePath, prefix) {
  const normalizedPath = normalizePolicyPrefix(filePath);
  const normalizedPrefix = normalizePolicyPrefix(prefix);
  if (normalizedPrefix === '.') return true;
  return normalizedPath === normalizedPrefix || normalizedPath.startsWith(`${normalizedPrefix}/`);
}

function pathPolicyFinding(filePath, policy) {
  const deniedPrefixes = policy.pathPolicy?.deniedPrefixes || [];
  const allowedPrefixes = policy.pathPolicy?.allowedPrefixes || [];
  const deniedBy = deniedPrefixes.find((prefix) => pathMatchesPrefix(filePath, prefix));
  if (deniedBy) {
    return { severity: 'error', code: 'loop-policy-denied-path', message: `Loop path is denied by policy: ${filePath} (matched ${deniedBy})` };
  }
  if (allowedPrefixes.length > 0 && !allowedPrefixes.some((prefix) => pathMatchesPrefix(filePath, prefix))) {
    return { severity: 'error', code: 'loop-policy-path-not-allowed', message: `Loop path is outside the policy allow list: ${filePath}` };
  }
  return null;
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
      modifiedFiles: Array.isArray(iteration.actionHook?.modifiedFiles)
        ? iteration.actionHook.modifiedFiles.map((filePath, fileIndex) => normalizeReferencePathForReport(filePath, `${iteration.id || `iteration-${index}`}.actionHook.modifiedFiles[${fileIndex}]`))
        : [],
    },
    validation: {
      command: validation.command || 'not-run',
      expectedStatus: validation.expectedStatus || 'pass',
      actualStatus: validation.actualStatus || 'not-run',
      ...(validation.rawOutputPath ? { rawOutputPath: normalizeReferencePathForReport(validation.rawOutputPath, `${iteration.id || `iteration-${index}`}.validation.rawOutputPath`) } : {}),
      ...(validation.failureSignature ? { failureSignature: validation.failureSignature } : {}),
    },
    observedEvidence: Array.isArray(iteration.observedEvidence) && iteration.observedEvidence.length > 0
      ? iteration.observedEvidence.map((evidence, evidenceIndex) => normalizeEvidence(evidence, `${iteration.id || `iteration-${index}`}.observedEvidence[${evidenceIndex}].path`))
      : [normalizeEvidence(null, `${iteration.id || `iteration-${index}`}.observedEvidence[0].path`)],
    findings,
    observability: {
      elapsedSeconds: Number.isFinite(iteration.observability?.elapsedSeconds) ? iteration.observability.elapsedSeconds : 0,
      blockedToActionableSeconds: Number.isFinite(iteration.observability?.blockedToActionableSeconds)
        ? iteration.observability.blockedToActionableSeconds
        : null,
    },
    decision: iteration.decision || 'continue',
    nextRecommendedAction: iteration.nextRecommendedAction || 'Continue to the next loop iteration.',
  };
}

function buildReviewBody(summary) {
  const lines = [
    `Result: ${summary.result}`,
    `Stop reason: ${summary.stopReason}`,
    `Iterations: ${summary.summary.iterationCount}`,
    `Policy: ${summary.policy.policyId} (${summary.policy.sourcePath})`,
    `Authority: report-only evidence; human review and required checks remain authoritative.`,
    `Next action: ${summary.nextRecommendedAction}`,
  ];
  if (summary.observability.repeatedFailureSignatures.length > 0) {
    lines.push('Repeated failure signatures:');
    for (const signature of summary.observability.repeatedFailureSignatures.slice(0, 5)) {
      lines.push(`- ${signature.signature}: ${signature.count} occurrence(s)`);
    }
  }
  if (summary.findings.length > 0) {
    lines.push('Findings:');
    for (const finding of summary.findings.slice(0, 5)) {
      lines.push(`- [${finding.severity}] ${finding.code}: ${finding.message}`);
    }
  }
  return lines.join('\n');
}

function createObservabilityState() {
  return {
    elapsedSeconds: 0,
    modifiedFiles: new Set(),
    missingEvidenceIds: new Set(),
    deniedCommands: new Set(),
    deniedPaths: new Set(),
    highRiskEscalations: 0,
    unsafeActionStops: 0,
    repeatedFailures: new Map(),
    blockedToActionableSeconds: [],
  };
}

function recordFailureSignature(state, iteration) {
  const signature = iteration.validation.failureSignature;
  if (!signature || iteration.validation.actualStatus === 'pass') return null;
  const current = state.repeatedFailures.get(signature) || {
    signature,
    count: 0,
    firstIteration: iteration.id,
    lastIteration: iteration.id,
  };
  current.count += 1;
  current.lastIteration = iteration.id;
  state.repeatedFailures.set(signature, current);
  return current;
}

function visibleEvidenceIds(iterations) {
  const ids = new Set();
  for (const iteration of iterations) {
    for (const evidence of iteration.observedEvidence) {
      if (evidence.status !== 'not_collected') ids.add(evidence.id);
    }
  }
  return ids;
}

function evaluatePolicyForIteration({ input, iteration, iterations, policy, state }) {
  const findings = [];
  const stopRules = policy.stopRules || {};
  const commandFinding = commandPolicyFinding(iteration.validation.command, policy);
  if (commandFinding) {
    findings.push(commandFinding);
    state.deniedCommands.add(iteration.validation.command);
    if (stopRules.stopOnDeniedCommand) return { stopReason: 'unsafe-action', findings };
  }

  const candidatePaths = [
    iteration.validation.rawOutputPath,
    ...iteration.observedEvidence.map((evidence) => evidence.path),
    ...iteration.actionHook.modifiedFiles,
  ].filter(Boolean);
  for (const candidatePath of candidatePaths) {
    const finding = pathPolicyFinding(candidatePath, policy);
    if (finding) {
      findings.push(finding);
      state.deniedPaths.add(candidatePath);
    }
  }
  if (findings.some((finding) => finding.code === 'loop-policy-denied-path' || finding.code === 'loop-policy-path-not-allowed') && stopRules.stopOnDeniedPath) {
    return { stopReason: 'unsafe-action', findings };
  }

  const modifiedFileLimit = policy.budgets?.modifiedFileLimit ?? 0;
  for (const modifiedFile of iteration.actionHook.modifiedFiles) state.modifiedFiles.add(modifiedFile);
  if (state.modifiedFiles.size > modifiedFileLimit) {
    findings.push({
      severity: 'error',
      code: 'loop-policy-modified-file-limit',
      message: `Modified file count ${state.modifiedFiles.size} exceeds loop policy limit ${modifiedFileLimit}.`,
    });
    return { stopReason: 'unsafe-action', findings };
  }

  state.elapsedSeconds += iteration.observability.elapsedSeconds || 0;
  if (iteration.observability.blockedToActionableSeconds !== null) {
    state.blockedToActionableSeconds.push(iteration.observability.blockedToActionableSeconds);
  }
  const wallClockBudgetSeconds = policy.budgets?.wallClockBudgetSeconds ?? Number.POSITIVE_INFINITY;
  if (state.elapsedSeconds > wallClockBudgetSeconds) {
    findings.push({
      severity: 'warning',
      code: 'loop-policy-wall-clock-budget',
      message: `Observed fixture elapsed time ${state.elapsedSeconds}s exceeds loop policy budget ${wallClockBudgetSeconds}s.`,
    });
    return { stopReason: 'blocked', findings };
  }

  const repeated = recordFailureSignature(state, iteration);
  const repeatedFailureThreshold = stopRules.repeatedFailureThreshold || Number.POSITIVE_INFINITY;
  if (repeated && repeated.count >= repeatedFailureThreshold) {
    findings.push({
      severity: 'warning',
      code: 'loop-policy-repeated-failure',
      message: `Failure signature ${repeated.signature} repeated ${repeated.count} time(s).`,
    });
    return { stopReason: 'blocked', findings };
  }

  const requiredEvidenceIds = policy.evidenceRequirements?.requiredEvidenceIds || [];
  const observedEvidenceIds = visibleEvidenceIds(iterations);
  for (const evidenceId of requiredEvidenceIds) {
    if (!observedEvidenceIds.has(evidenceId)) state.missingEvidenceIds.add(evidenceId);
    else state.missingEvidenceIds.delete(evidenceId);
  }
  const missingEvidenceStops = Boolean(policy.evidenceRequirements?.missingEvidenceStops || stopRules.stopOnMissingEvidence);
  if (missingEvidenceStops && state.missingEvidenceIds.size > 0) {
    findings.push({
      severity: 'warning',
      code: 'loop-policy-missing-evidence',
      message: `Required evidence missing: ${[...state.missingEvidenceIds].sort().join(', ')}`,
    });
    return { stopReason: 'blocked', findings };
  }

  const riskLevel = input.goal?.riskLevel || 'low';
  const approvalEvidenceIds = policy.humanApproval?.approvalEvidenceIds || [];
  const requiresHumanApproval = (policy.humanApproval?.requiredRiskLevels || []).includes(riskLevel);
  const hasApprovalEvidence = approvalEvidenceIds.some((evidenceId) => observedEvidenceIds.has(evidenceId));
  if (requiresHumanApproval && !hasApprovalEvidence) {
    state.highRiskEscalations += 1;
    findings.push({
      severity: 'warning',
      code: 'loop-policy-human-approval-required',
      message: `Risk level ${riskLevel} requires human approval evidence before loop continuation.`,
    });
    if (stopRules.stopOnHighRiskEscalation) return { stopReason: 'human-required', findings };
  }

  return { stopReason: null, findings };
}

function buildObservability({ iterations, state, stopReason }) {
  const repeatedFailureSignatures = [...state.repeatedFailures.values()]
    .filter((signature) => signature.count > 1)
    .sort((a, b) => a.signature.localeCompare(b.signature));
  const blockedToActionableSeconds = state.blockedToActionableSeconds.length > 0
    ? Math.max(...state.blockedToActionableSeconds)
    : null;
  return {
    verificationSequence: iterations.map((iteration) => iteration.validation.actualStatus),
    elapsedSecondsObserved: state.elapsedSeconds,
    blockedToActionable: {
      status: blockedToActionableSeconds === null ? 'not_collected' : 'collected',
      seconds: blockedToActionableSeconds,
    },
    repeatedFailureSignatures,
    unsafeActionStops: stopReason === 'unsafe-action' ? state.unsafeActionStops + 1 : state.unsafeActionStops,
    missingEvidenceIds: [...state.missingEvidenceIds].sort(),
    deniedCommands: [...state.deniedCommands].sort(),
    deniedPaths: [...state.deniedPaths].sort(),
    modifiedFileCount: state.modifiedFiles.size,
    highRiskEscalations: state.highRiskEscalations,
    approvalAuthority: 'none; loop summaries are report-only and do not replace human approval or required checks',
  };
}

function buildLoopRun(options = parseArgs()) {
  const inputPath = assertContainedInputPath(options.input, 'loop input');
  const input = readJson(inputPath, 'loop input');
  assertSchemaValid(input, INPUT_SCHEMA_PATH, 'loop input');
  assertLoopInput(input);
  const { policy, sourcePath: policySourcePath } = loadLoopPolicy(options, input);

  const generatedAt = options.generatedAt || new Date().toISOString();
  const requestedMaxIterations = options.maxIterations || input.maxIterations || input.iterations.length;
  const policyMaxIterations = policy.budgets?.maxIterations || requestedMaxIterations;
  const maxIterations = Math.min(requestedMaxIterations, policyMaxIterations);
  const detectedForbidden = forbiddenActions(input);
  const iterations = [];
  const allFindings = [];
  const observabilityState = createObservabilityState();
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
      const policyResult = evaluatePolicyForIteration({
        input,
        iteration,
        iterations,
        policy,
        state: observabilityState,
      });
      if (policyResult.findings.length > 0) {
        allFindings.push(...policyResult.findings);
      }
      if (policyResult.stopReason) {
        stopReason = policyResult.stopReason;
        nextRecommendedAction = policyResult.stopReason === 'unsafe-action'
          ? 'Stop the loop and update the loop policy, command, path, or action hook before retrying.'
          : 'Stop the loop and collect the missing approval/evidence or adjust the plan before retrying.';
        break;
      }
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

  if (!stopReason && requestedMaxIterations > maxIterations && iterations.length >= maxIterations) {
    allFindings.push({
      severity: 'warning',
      code: 'loop-policy-max-iterations',
      message: `Loop policy limited this run to ${maxIterations} iteration(s) from requested maxIterations=${requestedMaxIterations}.`,
    });
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
  const inputHash = sha256(stableJson(input));
  const policyHash = sha256(stableJson(policy));
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
        riskLevel: input.goal.riskLevel || 'low',
      },
      execPlan: {
        planId: input.execPlan.planId,
        path: normalizeReferencePathForReport(input.execPlan.path, 'execPlan.path'),
      },
      contextPackRefs: Array.isArray(input.contextPackRefs)
        ? input.contextPackRefs.map((ref, index) => normalizeReferencePathForReport(ref, `contextPackRefs[${index}]`))
        : [],
      maxIterations,
      ...(input.policyRef ? { policyRef: normalizeReferencePathForReport(input.policyRef, 'policyRef') } : {}),
    },
    policy: {
      schemaVersion: policy.schemaVersion,
      policyId: policy.policyId,
      sourcePath: policySourcePath,
      reportOnly: policy.reportOnly,
      budgets: {
        requestedMaxIterations,
        effectiveMaxIterations: maxIterations,
        wallClockBudgetSeconds: policy.budgets.wallClockBudgetSeconds,
        modifiedFileLimit: policy.budgets.modifiedFileLimit,
      },
      stopRules: {
        stopOnDeniedCommand: Boolean(policy.stopRules.stopOnDeniedCommand),
        stopOnDeniedPath: Boolean(policy.stopRules.stopOnDeniedPath),
        stopOnMissingEvidence: Boolean(policy.stopRules.stopOnMissingEvidence),
        stopOnHighRiskEscalation: Boolean(policy.stopRules.stopOnHighRiskEscalation),
        repeatedFailureThreshold: policy.stopRules.repeatedFailureThreshold,
      },
      privacy: {
        redactionMode: policy.privacy.redactionMode,
        publicRawLogsAllowed: Boolean(policy.privacy.publicRawLogsAllowed),
      },
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
      unsafeActionStopCount: stopReason === 'unsafe-action' ? 1 : 0,
      repeatedFailureSignatureCount: [...observabilityState.repeatedFailures.values()].filter((signature) => signature.count > 1).length,
    },
    iterations,
    commands,
    findings: allFindings,
    observability: buildObservability({ iterations, state: observabilityState, stopReason }),
    replay: {
      inputHash,
      policyHash,
      idempotencyKey: sha256(`${input.runId || 'loop-run'}:${generatedAt}:${inputHash}:${policyHash}`),
      note: 'Re-run with the same input, policy, and generatedAt to reproduce deterministic fixture summaries.',
    },
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
    `- Risk level: \`${summary.input.goal.riskLevel}\``,
    `- Next recommended action: ${summary.nextRecommendedAction}`,
    '',
    '## Policy',
    '',
    `- Policy: \`${summary.policy.policyId}\` (${summary.policy.sourcePath})`,
    `- Effective max iterations: ${summary.policy.budgets.effectiveMaxIterations} (requested ${summary.policy.budgets.requestedMaxIterations})`,
    `- Wall-clock budget: ${summary.policy.budgets.wallClockBudgetSeconds}s`,
    `- Modified file limit: ${summary.policy.budgets.modifiedFileLimit}`,
    `- Redaction mode: \`${summary.policy.privacy.redactionMode}\``,
    `- Public raw logs allowed: ${summary.policy.privacy.publicRawLogsAllowed}`,
    '',
    '## Safety',
    '',
    `- Worktree mode: \`${summary.safety.worktreeMode}\``,
    `- Mutations allowed: ${summary.safety.mutationsAllowed}`,
    `- Hosted LLM calls allowed: ${summary.safety.hostedLlmCallsAllowed}`,
    `- Auto-merge allowed: ${summary.safety.autoMergeAllowed}`,
    `- Forbidden actions detected: ${summary.safety.forbiddenActionsDetected.length > 0 ? summary.safety.forbiddenActionsDetected.join(', ') : 'none'}`,
    '',
    '## Observability',
    '',
    `- Verification sequence: ${summary.observability.verificationSequence.length > 0 ? summary.observability.verificationSequence.join(' -> ') : 'none'}`,
    `- Elapsed seconds observed: ${summary.observability.elapsedSecondsObserved}`,
    `- Blocked-to-actionable: ${summary.observability.blockedToActionable.status}${summary.observability.blockedToActionable.seconds === null ? '' : ` (${summary.observability.blockedToActionable.seconds}s)`}`,
    `- Unsafe-action stops: ${summary.observability.unsafeActionStops}`,
    `- Missing evidence IDs: ${summary.observability.missingEvidenceIds.length > 0 ? summary.observability.missingEvidenceIds.join(', ') : 'none'}`,
    `- Denied commands: ${summary.observability.deniedCommands.length > 0 ? summary.observability.deniedCommands.join(' | ') : 'none'}`,
    `- Denied paths: ${summary.observability.deniedPaths.length > 0 ? summary.observability.deniedPaths.join(', ') : 'none'}`,
    `- Modified file count: ${summary.observability.modifiedFileCount}`,
    `- High-risk escalations: ${summary.observability.highRiskEscalations}`,
    `- Approval authority: ${summary.observability.approvalAuthority}`,
    '',
    '## Iterations',
    '',
  ];
  for (const iteration of summary.iterations) {
    lines.push(`### ${iteration.index}. ${iteration.id}`);
    lines.push('');
    lines.push(`- Planned action: ${iteration.plannedAction}`);
    lines.push(`- Action hook: ${iteration.actionHook.kind} — ${iteration.actionHook.description}`);
    if (iteration.actionHook.modifiedFiles.length > 0) {
      lines.push(`- Modified files: ${iteration.actionHook.modifiedFiles.map((filePath) => `\`${filePath}\``).join(', ')}`);
    }
    lines.push(`- Validation: \`${iteration.validation.command}\` (${iteration.validation.actualStatus}; expected ${iteration.validation.expectedStatus})`);
    if (iteration.validation.failureSignature) {
      lines.push(`- Failure signature: \`${iteration.validation.failureSignature}\``);
    }
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
  lines.push('', '## Repeated failure signatures', '');
  if (summary.observability.repeatedFailureSignatures.length === 0) lines.push('- none');
  for (const signature of summary.observability.repeatedFailureSignatures) {
    lines.push(`- \`${signature.signature}\`: ${signature.count} occurrence(s), ${signature.firstIteration} -> ${signature.lastIteration}`);
  }
  lines.push('', '## Replay', '');
  lines.push(`- Input hash: \`${summary.replay.inputHash}\``);
  lines.push(`- Policy hash: \`${summary.replay.policyHash}\``);
  lines.push(`- Idempotency key: \`${summary.replay.idempotencyKey}\``);
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
