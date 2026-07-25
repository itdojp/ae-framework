import { createHash } from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';

export const FORMAL_RUNNER_RESULT_SCHEMA_VERSION = 'formal-runner-result/v1';
export const FORMAL_RUNNER_OUTPUT_SCHEMA_VERSION = 'formal-runner-output/v1';
export const FORMAL_RUNNER_OUTPUT_CONTRACT_ID = 'formal-runner-output.v1';

export const FORMAL_VERIFICATION_KINDS = Object.freeze([
  'presence',
  'build',
  'typecheck',
  'conformance',
  'model-check',
  'proof-check',
]);

const PLACEHOLDER_VERSIONS = new Set([
  '',
  'unknown',
  'unspecified',
  'n/a',
  'na',
  'none',
  'null',
]);

export const FORMAL_RUNNER_PRODUCERS = Object.freeze({
  tla: Object.freeze({
    id: 'ae.formal.verify-tla',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/verify-tla.mjs',
  }),
  alloy: Object.freeze({
    id: 'ae.formal.verify-alloy',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/verify-alloy.mjs',
  }),
  apalache: Object.freeze({
    id: 'ae.formal.verify-apalache',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/verify-apalache.mjs',
  }),
  smt: Object.freeze({
    id: 'ae.formal.verify-smt',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/verify-smt.mjs',
  }),
  conformance: Object.freeze({
    id: 'ae.formal.verify-conformance',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/verify-conformance.mjs',
  }),
  conformanceDriver: Object.freeze({
    id: 'ae.formal.conformance-driver',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/conformance-driver.mjs',
  }),
  kani: Object.freeze({
    id: 'ae.formal.verify-kani',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/verify-kani.mjs',
  }),
  spin: Object.freeze({
    id: 'ae.formal.verify-spin',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/verify-spin.mjs',
  }),
  csp: Object.freeze({
    id: 'ae.formal.verify-csp',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/verify-csp.mjs',
  }),
  cspModelCheck: Object.freeze({
    id: 'ae.formal.verify-csp-model-check',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/verify-csp.mjs',
  }),
  lean: Object.freeze({
    id: 'ae.formal.verify-lean',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/formal/verify-lean.mjs',
  }),
  model: Object.freeze({
    id: 'ae.formal.run-model-checks',
    version: '1.0.0',
    contract: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactRef: 'scripts/verify/run-model-checks.mjs',
  }),
});

const FORMAL_RUNNER_VERIFICATION_KINDS = Object.freeze({
  tla: Object.freeze(['model-check']),
  alloy: Object.freeze(['model-check']),
  apalache: Object.freeze(['model-check']),
  smt: Object.freeze(['model-check']),
  conformance: Object.freeze(['conformance']),
  conformanceDriver: Object.freeze(['conformance']),
  kani: Object.freeze(['presence']),
  spin: Object.freeze(['model-check']),
  csp: Object.freeze(['typecheck']),
  cspModelCheck: Object.freeze(['model-check']),
  lean: Object.freeze(['build']),
  model: Object.freeze(['model-check']),
});

export function getFormalRunnerProducer(runner) {
  const producer = FORMAL_RUNNER_PRODUCERS[runner];
  if (!producer) {
    throw new Error(`Unknown formal runner producer: ${runner}`);
  }
  return { ...producer };
}

export function getFormalRunnerVerificationKinds(runner) {
  const kinds = FORMAL_RUNNER_VERIFICATION_KINDS[runner];
  if (!kinds) {
    throw new Error(`Unknown formal runner verification policy: ${runner}`);
  }
  return [...kinds];
}

export function hasReviewedFormalVerificationKind(runner, verificationKind) {
  try {
    return getFormalRunnerVerificationKinds(runner).includes(String(verificationKind ?? '').trim());
  } catch {
    return false;
  }
}

export function claimEligibilityForVerificationKind(verificationKind) {
  switch (verificationKind) {
    case 'conformance':
      return 'conformance';
    case 'model-check':
      return 'model';
    case 'proof-check':
      return 'proof';
    case 'presence':
    case 'build':
    case 'typecheck':
    default:
      return 'none';
  }
}

export function hasEligibleFormalSemanticResult(runner, semanticResult) {
  if (runner === 'smt') {
    return semanticResult?.domain === 'smt'
      && semanticResult.parsed === true
      && ['sat', 'unsat'].includes(semanticResult.expectedResult)
      && semanticResult.actualResult === semanticResult.expectedResult
      && semanticResult.matchesExpected === true
      && semanticResult.timeout === false;
  }
  if (runner === 'spin') {
    return semanticResult?.domain === 'spin'
      && semanticResult.parsed === true
      && semanticResult.errors === 0
      && semanticResult.trailPresent === false
      && semanticResult.counterexamplePresent === false
      && semanticResult.searchCompleted === true
      && semanticResult.propertyMatched === true
      && semanticResult.boundsMatched === true
      && semanticResult.timeout === false;
  }
  return true;
}

export function extractToolVersion(output) {
  const text = String(output ?? '').trim();
  if (!text) return '';
  const semantic = text.match(/\bv?(\d+\.\d+(?:\.\d+)?(?:[-+][0-9A-Za-z.-]+)?)\b/u);
  if (semantic) return semantic[1];
  return '';
}

export function sha256FileSync(filePath) {
  return createHash('sha256').update(fs.readFileSync(filePath)).digest('hex');
}

export function readPackageVersion(repoRoot = process.cwd()) {
  try {
    const payload = JSON.parse(fs.readFileSync(path.join(repoRoot, 'package.json'), 'utf8'));
    return typeof payload.version === 'string' ? payload.version.trim() : '';
  } catch {
    return '';
  }
}

export function normalizeToolVersion({
  version,
  source = 'unavailable',
  artifactSha256 = null,
  expectedArtifactSha256 = null,
} = {}) {
  const normalizedVersion = String(version ?? '').trim();
  const normalizedSource = String(source ?? 'unavailable').trim() || 'unavailable';
  const normalizedArtifactSha = typeof artifactSha256 === 'string' && artifactSha256.trim()
    ? artifactSha256.trim().toLowerCase()
    : null;
  const normalizedExpectedSha = typeof expectedArtifactSha256 === 'string' && expectedArtifactSha256.trim()
    ? expectedArtifactSha256.trim().toLowerCase()
    : null;
  const placeholder = PLACEHOLDER_VERSIONS.has(normalizedVersion.toLowerCase());
  const artifactPinMismatch = Boolean(normalizedExpectedSha)
    && (!normalizedArtifactSha || normalizedArtifactSha !== normalizedExpectedSha);
  const incompleteReviewedPin = normalizedSource === 'reviewed-pin'
    && (!normalizedArtifactSha || !normalizedExpectedSha);
  const sourceEligible = ['cli', 'jar-manifest', 'package-manifest', 'reviewed-pin'].includes(normalizedSource);
  const versionStatus = artifactPinMismatch || incompleteReviewedPin
    ? 'mismatch'
    : (!placeholder && sourceEligible ? 'verified' : 'unknown');

  return {
    version: placeholder ? 'unknown' : normalizedVersion,
    versionStatus,
    versionSource: normalizedSource,
    ...(normalizedArtifactSha ? { artifactSha256: normalizedArtifactSha } : {}),
    ...(normalizedExpectedSha ? { expectedArtifactSha256: normalizedExpectedSha } : {}),
  };
}

export function hasEligibleToolVersion(tool) {
  if (!tool || typeof tool !== 'object' || Array.isArray(tool)) return false;
  const version = String(tool.version ?? '').trim().toLowerCase();
  const source = String(tool.versionSource ?? '').trim();
  if (tool.versionStatus !== 'verified' || PLACEHOLDER_VERSIONS.has(version)) return false;
  if (!['cli', 'jar-manifest', 'package-manifest', 'reviewed-pin'].includes(source)) return false;
  if (source !== 'reviewed-pin') return true;
  const actual = String(tool.artifactSha256 ?? '').trim().toLowerCase();
  const expected = String(tool.expectedArtifactSha256 ?? '').trim().toLowerCase();
  return /^[a-f0-9]{64}$/u.test(actual) && actual === expected;
}

export function classifyFormalResult({ status, ok, executionOccurred } = {}) {
  const normalizedStatus = String(status ?? '').trim().toLowerCase();
  if (!executionOccurred) {
    if (['file_not_found', 'project_not_found', 'config_not_found', 'jar_not_found'].includes(normalizedStatus)) {
      return 'missing';
    }
    if ([
      'detected',
      'no_file',
      'not-run',
      'skipped',
      'solver_not_available',
      'tool_not_available',
      'compile_not_available',
      'java_not_available',
      'jar_not_set',
      'run_cmd_unsupported',
      'unsupported',
    ].includes(normalizedStatus)) {
      return 'skipped';
    }
    return 'unknown';
  }
  if (normalizedStatus === 'timeout') return 'timeout';
  if (['tool-error', 'tool_error', 'spawn-error', 'spawn_error', 'error'].includes(normalizedStatus)) {
    return executionOccurred ? 'tool-error' : 'skipped';
  }
  if (ok === true) return 'ok';
  if (ok === false || ['failed', 'gen_failed', 'compile_failed', 'invalid', 'validation_failed'].includes(normalizedStatus)) {
    return 'failed';
  }
  return 'unknown';
}

export function buildFormalExecutionEvidence({
  runner,
  verificationKind,
  toolName,
  toolVersion,
  versionSource,
  artifactSha256 = null,
  expectedArtifactSha256 = null,
  inputPaths,
  resultStatus,
  exitCode = null,
  logPath = null,
  scope,
  assumptions,
  executionOccurred,
  semanticResult,
}) {
  const occurred = executionOccurred === true;
  const normalizedResultStatus = String(resultStatus ?? '').trim() || 'unknown';
  const producer = getFormalRunnerProducer(runner);
  const allowedVerificationKinds = getFormalRunnerVerificationKinds(runner);
  const normalizedVerificationKind = String(verificationKind ?? allowedVerificationKinds[0] ?? '').trim();
  if (!allowedVerificationKinds.includes(normalizedVerificationKind)) {
    throw new TypeError(
      `verificationKind ${normalizedVerificationKind || '(missing)'} is not allowed for reviewed runner ${runner}`,
    );
  }
  const version = normalizeToolVersion({
    version: toolVersion,
    source: versionSource,
    artifactSha256,
    expectedArtifactSha256,
  });
  const normalizedInputs = Array.from(new Set((Array.isArray(inputPaths) ? inputPaths : [inputPaths])
    .map((value) => typeof value === 'string' ? value.trim() : '')
    .filter(Boolean)));
  const normalizedAssumptions = Array.from(new Set((Array.isArray(assumptions) ? assumptions : [assumptions])
    .map((value) => typeof value === 'string' ? value.trim() : '')
    .filter(Boolean)));

  return {
    schemaVersion: FORMAL_RUNNER_RESULT_SCHEMA_VERSION,
    artifactStatus: occurred ? 'execution-report' : 'not-executed',
    producer,
    provenance: 'runner-reported',
    executionOccurred: occurred,
    verificationKind: normalizedVerificationKind,
    tool: {
      name: String(toolName ?? '').trim() || runner,
      ...version,
    },
    input: normalizedInputs,
    result: {
      status: normalizedResultStatus,
      code: Number.isInteger(exitCode) ? exitCode : null,
      logPath: typeof logPath === 'string' && logPath.trim() ? logPath.trim() : null,
    },
    scope: String(scope ?? '').trim(),
    assumptions: normalizedAssumptions,
    ...(semanticResult === undefined ? {} : { semanticResult: JSON.parse(JSON.stringify(semanticResult)) }),
  };
}

export function buildFormalRunnerOutput({ runner, executionEvidence }) {
  const producer = getFormalRunnerProducer(runner);
  if (!executionEvidence || typeof executionEvidence !== 'object' || Array.isArray(executionEvidence)) {
    throw new TypeError('executionEvidence must be an object');
  }
  const evidenceProducer = executionEvidence.producer;
  if (!evidenceProducer
    || evidenceProducer.id !== producer.id
    || evidenceProducer.version !== producer.version
    || evidenceProducer.contract !== producer.contract
    || evidenceProducer.artifactRef !== producer.artifactRef) {
    throw new TypeError('executionEvidence producer does not match the reviewed runner');
  }
  if (executionEvidence.provenance !== 'runner-reported' || executionEvidence.adapter !== undefined) {
    throw new TypeError('runner output requires unadapted runner-reported evidence');
  }
  if (!hasReviewedFormalVerificationKind(runner, executionEvidence.verificationKind)) {
    throw new TypeError('executionEvidence verificationKind is not allowed for the reviewed runner');
  }
  if (runner === 'smt' && executionEvidence.semanticResult?.domain !== 'smt') {
    throw new TypeError('SMT runner output requires bound SMT semanticResult evidence');
  }
  if (runner === 'spin' && executionEvidence.semanticResult?.domain !== 'spin') {
    throw new TypeError('SPIN runner output requires bound SPIN semanticResult evidence');
  }
  if (executionEvidence.result?.status === 'ok'
    && !hasEligibleFormalSemanticResult(runner, executionEvidence.semanticResult)) {
    throw new TypeError('successful runner output requires eligible semantic result evidence');
  }
  return {
    schemaVersion: FORMAL_RUNNER_OUTPUT_SCHEMA_VERSION,
    contractId: FORMAL_RUNNER_OUTPUT_CONTRACT_ID,
    artifactStatus: executionEvidence.artifactStatus,
    producer,
    executionEvidence,
  };
}

export function buildLegacyFormalExecutionEvidence({
  runner,
  verificationKind,
  toolName,
  toolVersion,
  versionSource,
  artifactSha256 = null,
  expectedArtifactSha256 = null,
  inputPaths,
  status,
  ok,
  ran,
  attempted,
  exitCode = null,
  logPath = null,
  scope,
  assumptions,
  semanticResult,
}) {
  const normalizedStatus = String(status ?? '').trim().toLowerCase();
  const executionOccurred = attempted === true
    || ran === true
    || ['ran', 'failed', 'timeout', 'tool-error', 'tool_error', 'error', 'gen_failed', 'compile_failed'].includes(normalizedStatus);
  const resultStatus = classifyFormalResult({ status: normalizedStatus, ok, executionOccurred });
  return buildFormalExecutionEvidence({
    runner,
    verificationKind,
    toolName,
    toolVersion,
    versionSource,
    artifactSha256,
    expectedArtifactSha256,
    inputPaths,
    resultStatus,
    exitCode,
    logPath,
    scope,
    assumptions,
    executionOccurred,
    semanticResult,
  });
}
