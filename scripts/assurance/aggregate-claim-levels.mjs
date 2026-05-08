#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { normalizeArtifactPath as normalizeSharedArtifactPath } from '../ci/lib/path-normalization.mjs';

export const DEFAULT_CLAIM_EVIDENCE_MANIFEST = 'artifacts/assurance/claim-evidence-manifest.json';
export const DEFAULT_POLICY_GATE_SUMMARY = 'artifacts/ci/policy-gate-summary.json';
export const DEFAULT_CHANGE_PACKAGE_V2 = 'artifacts/change-package/change-package-v2.json';
export const DEFAULT_OUTPUT_JSON = 'artifacts/assurance/claim-level-summary.json';
export const DEFAULT_OUTPUT_MD = 'artifacts/assurance/claim-level-summary.md';
export const DEFAULT_SCHEMA = 'schema/claim-level-summary-v1.schema.json';

const SCHEMA_VERSION = 'claim-level-summary/v1';
const LEVELS = ['A0', 'A1', 'A2', 'A3', 'A4'];
const CLAIM_STATES = new Set([
  'satisfied',
  'tested',
  'model-checked',
  'proved',
  'runtime-mitigated',
  'waived',
  'unresolved',
  'failed',
  'not-applicable',
]);
const CHANGE_PACKAGE_STATES = new Set(['proved', 'model-checked', 'tested', 'runtime-mitigated', 'waived', 'unresolved']);
const DECISION_RESULTS = new Set(['pass', 'waived', 'report-only', 'block']);
const DECISION_MODES = new Set(['report-only', 'strict']);
const REPO_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const EVIDENCE_KINDS = new Set([
  'spec',
  'behavior',
  'adversarial',
  'model',
  'proof',
  'runtime',
  'quality',
  'trace',
  'policy',
  'manual',
  'other',
]);
const CRITICALITIES = new Set(['low', 'medium', 'high', 'critical']);

function usage() {
  process.stdout.write(`Usage: node scripts/assurance/aggregate-claim-levels.mjs [options]\n\nOptions:\n  --claim-evidence-manifest <path>  claim-evidence-manifest/v1 input (default: ${DEFAULT_CLAIM_EVIDENCE_MANIFEST})\n  --policy-gate-summary <path>      optional policy-gate-summary/v1 input (default probe: ${DEFAULT_POLICY_GATE_SUMMARY})\n  --change-package <path>           optional change-package/v2 input (default probe: ${DEFAULT_CHANGE_PACKAGE_V2})\n  --temporary-override <path>       optional temporary-override/v1 input; repeatable\n  --output-json <path>              output JSON path (default: ${DEFAULT_OUTPUT_JSON})\n  --output-md <path>                output Markdown path (default: ${DEFAULT_OUTPUT_MD})\n  --schema <path>                   schema used for output validation (default: ${DEFAULT_SCHEMA})\n  --generated-at <iso-date-time>    override generatedAt for deterministic tests\n  --repository <owner/name>         source repository override\n  --pr-number <number>              source PR number override\n  --base-ref <ref>                  source base ref override\n  --head-ref <ref>                  source head ref override\n  --head-sha <sha>                  source head SHA override\n  --no-validate                     skip schema validation before writing\n  --help                            show this help\n`);
}

function readRequiredValue(argv, index, flag) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`${flag} requires a value`);
  }
  return next;
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    claimEvidenceManifest: DEFAULT_CLAIM_EVIDENCE_MANIFEST,
    policyGateSummary: DEFAULT_POLICY_GATE_SUMMARY,
    changePackage: DEFAULT_CHANGE_PACKAGE_V2,
    temporaryOverrides: [],
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    schema: DEFAULT_SCHEMA,
    generatedAt: null,
    repository: null,
    prNumber: null,
    baseRef: null,
    headRef: null,
    headSha: null,
    validate: true,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--claim-evidence-manifest') {
      options.claimEvidenceManifest = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--policy-gate-summary') {
      options.policyGateSummary = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--change-package') {
      options.changePackage = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--temporary-override') {
      options.temporaryOverrides.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--schema') {
      options.schema = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--repository') {
      options.repository = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--pr-number') {
      options.prNumber = Number.parseInt(readRequiredValue(argv, index, arg), 10);
      if (!Number.isSafeInteger(options.prNumber) || options.prNumber < 1) {
        throw new Error('--pr-number must be a positive integer');
      }
      index += 1;
      continue;
    }
    if (arg === '--base-ref') {
      options.baseRef = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--head-ref') {
      options.headRef = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--head-sha') {
      options.headSha = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--no-validate') {
      options.validate = false;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  return options;
}

function compareString(left, right) {
  return left < right ? -1 : left > right ? 1 : 0;
}

function ensureDateTime(value, label = 'generatedAt') {
  const raw = String(value ?? '').trim();
  if (!raw || !Number.isFinite(Date.parse(raw))) {
    throw new Error(`${label} must be an ISO date-time: ${raw || '(empty)'}`);
  }
  return new Date(raw).toISOString();
}

function readJson(targetPath) {
  return JSON.parse(fs.readFileSync(targetPath, 'utf8'));
}

function writeText(targetPath, content) {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
}

function writeJson(targetPath, payload) {
  writeText(targetPath, `${JSON.stringify(payload, null, 2)}\n`);
}

function existsFile(targetPath) {
  return Boolean(targetPath) && fs.existsSync(targetPath) && fs.statSync(targetPath).isFile();
}

function normalizeArtifactPath(value, label = 'artifact path') {
  const raw = String(value ?? '').trim();
  if (!raw) {
    throw new Error(`${label} must be a non-empty path`);
  }
  const posix = normalizeSharedArtifactPath(raw, { repoRoot: REPO_ROOT });
  if (
    !posix
    || posix.startsWith('/')
    || posix.startsWith('//')
    || posix.includes('..')
    || posix.includes('//')
    || /^[A-Za-z]:\//u.test(posix)
  ) {
    throw new Error(`${label} must be a relative normalized artifact path: ${raw}`);
  }
  return posix;
}

function resolveRequiredArtifact(inputPath, label) {
  const resolvedPath = path.resolve(inputPath);
  if (!existsFile(resolvedPath)) {
    throw new Error(`${label} not found at ${resolvedPath}`);
  }
  return {
    path: normalizeArtifactPath(inputPath, `${label} path`),
    present: true,
    payload: readJson(resolvedPath),
  };
}

function resolveOptionalArtifact(inputPath) {
  if (!inputPath) {
    return { path: null, present: false, payload: null };
  }
  const resolvedPath = path.resolve(inputPath);
  if (!existsFile(resolvedPath)) {
    return { path: null, present: false, payload: null };
  }
  return {
    path: normalizeArtifactPath(inputPath),
    present: true,
    payload: readJson(resolvedPath),
  };
}

function schemaVersionOf(payload) {
  return typeof payload?.schemaVersion === 'string' ? payload.schemaVersion : null;
}

function asInputArtifact(artifact, required = false) {
  return {
    path: artifact.present ? artifact.path : null,
    schemaVersion: artifact.present ? schemaVersionOf(artifact.payload) : null,
    present: Boolean(artifact.present),
    required: Boolean(required),
  };
}

function ensureArray(value) {
  return Array.isArray(value) ? value : [];
}

function maybeString(value) {
  return value === null || value === undefined ? '' : String(value).trim();
}

function normalizeCriticality(value) {
  const candidate = maybeString(value).toLowerCase();
  return CRITICALITIES.has(candidate) ? candidate : 'medium';
}

function normalizeLevel(value, fallback = 'A0') {
  const candidate = maybeString(value).toUpperCase();
  return LEVELS.includes(candidate) ? candidate : fallback;
}

function normalizeEvidenceKind(value) {
  const candidate = maybeString(value).toLowerCase();
  return EVIDENCE_KINDS.has(candidate) ? candidate : 'other';
}

function normalizeDecisionResult(value, fallback = 'report-only') {
  const candidate = maybeString(value).toLowerCase();
  return DECISION_RESULTS.has(candidate) ? candidate : fallback;
}

function normalizeDecisionMode(value, fallback = 'report-only') {
  const candidate = maybeString(value).toLowerCase();
  return DECISION_MODES.has(candidate) ? candidate : fallback;
}

function uniqueById(entries) {
  const seen = new Set();
  const result = [];
  for (const entry of entries) {
    const id = maybeString(entry?.id);
    if (!id || seen.has(id)) continue;
    seen.add(id);
    result.push(entry);
  }
  return result.sort((left, right) => compareString(left.id, right.id));
}

function buildPolicyClaimMap(policyGateSummary) {
  const claims = ensureArray(policyGateSummary.payload?.evaluation?.assurance?.claims);
  return new Map(claims.map((claim) => [maybeString(claim.claimId), claim]).filter(([claimId]) => claimId));
}

function buildChangeClaimMap(changePackage) {
  const claims = ensureArray(changePackage.payload?.claims);
  return new Map(claims.map((claim) => [maybeString(claim.id), claim]).filter(([claimId]) => claimId));
}

function buildProofObligationsByClaim(changePackage) {
  const byClaim = new Map();
  for (const obligation of ensureArray(changePackage.payload?.proofObligations)) {
    const claimId = maybeString(obligation.claimId);
    if (!claimId) continue;
    const list = byClaim.get(claimId) ?? [];
    list.push(obligation);
    byClaim.set(claimId, list);
  }
  return byClaim;
}

function buildCounterexamplesByClaim(changePackage) {
  const byClaim = new Map();
  for (const counterexample of ensureArray(changePackage.payload?.counterexamples)) {
    for (const claimId of ensureArray(counterexample.claimIds).map(maybeString).filter(Boolean)) {
      const list = byClaim.get(claimId) ?? [];
      list.push(counterexample);
      byClaim.set(claimId, list);
    }
  }
  return byClaim;
}

function readTemporaryOverrides(paths) {
  return paths.map((entryPath) => {
    const artifact = resolveRequiredArtifact(entryPath, 'Temporary override');
    return {
      path: artifact.path,
      payload: artifact.payload,
    };
  }).sort((left, right) => compareString(left.path, right.path));
}

function buildOverrideIndexes(temporaryOverrides) {
  const byId = new Map();
  const byClaim = new Map();
  for (const override of temporaryOverrides) {
    const id = maybeString(override.payload?.id);
    if (id) byId.set(id, override);
    for (const claimId of ensureArray(override.payload?.relatedClaimIds).map(maybeString).filter(Boolean)) {
      const list = byClaim.get(claimId) ?? [];
      list.push(override);
      byClaim.set(claimId, list);
    }
  }
  return { byId, byClaim };
}

function parseNotApplicableMarker(claim) {
  for (const note of ensureArray(claim.notes)) {
    const raw = maybeString(note);
    const lower = raw.toLowerCase();
    if (!lower.startsWith('not-applicable:') && !lower.startsWith('applicability:not-applicable:')) {
      continue;
    }
    const body = raw.includes(':') ? raw.slice(raw.indexOf(':') + 1).trim() : raw;
    const segments = body.split('|').map((segment) => segment.trim()).filter(Boolean);
    const reason = segments[0]?.replace(/^not-applicable:/iu, '').trim() || 'Claim is explicitly out of scope.';
    const result = {
      reason,
      scope: `claim:${claim.id}`,
    };
    for (const segment of segments.slice(1)) {
      const [key, ...rest] = segment.split('=');
      const normalizedKey = maybeString(key).toLowerCase();
      const value = rest.join('=').trim();
      if (!value) continue;
      if (normalizedKey === 'scope') result.scope = value;
      if (normalizedKey === 'artifact' || normalizedKey === 'artifactpath') {
        result.artifactPath = normalizeArtifactPath(value, 'not-applicable artifact path');
      }
    }
    return result;
  }
  return null;
}

function normalizeEvidenceStatus(value) {
  const raw = maybeString(value).toLowerCase();
  if (['failed', 'failure', 'open', 'blocked'].includes(raw)) return 'failed';
  if (['stale', 'expired'].includes(raw)) return 'stale';
  if (['observed', 'passed', 'pass', 'success', 'closed', 'resolved', 'discharged'].includes(raw)) return 'observed';
  return null;
}

function inferEvidenceStatus(ref, state, policyClaim) {
  const explicitStatus = normalizeEvidenceStatus(ref?.status);
  if (explicitStatus) return explicitStatus;
  const policyEvidenceRefs = ensureArray(policyClaim?.evidenceRefs).map(maybeString);
  if (state === 'failed' && normalizeDecisionResult(policyClaim?.result, '') === 'block' && policyEvidenceRefs.includes(maybeString(ref?.id))) {
    return 'failed';
  }
  return 'observed';
}

function convertEvidenceRefs(claim, state, policyClaim) {
  return uniqueById(ensureArray(claim.evidenceRefs).map((ref, index) => ({
    id: maybeString(ref?.id) || `${claim.id}:evidence:${index}`,
    kind: normalizeEvidenceKind(ref?.kind),
    status: inferEvidenceStatus(ref, state, policyClaim),
    artifactPath: normalizeArtifactPath(ref?.artifactPath || `artifacts/assurance/${claim.id}/evidence-${index}.json`, 'evidence artifact path'),
    sourceArtifactId: maybeString(ref?.sourceArtifactId) || 'claim-evidence-manifest',
    description: maybeString(ref?.description) || `Evidence linked from claim-evidence manifest for ${claim.id}.`,
  })));
}

function convertMissingEvidenceRefs(claim) {
  return uniqueById(ensureArray(claim.missingEvidenceRefs).map((ref, index) => ({
    id: maybeString(ref?.id) || `${claim.id}:missing:${index}`,
    expectedKind: normalizeEvidenceKind(ref?.expectedKind),
    reason: maybeString(ref?.reason) || `Missing evidence for ${claim.id}.`,
    sourceArtifactId: maybeString(ref?.sourceArtifactId) || 'claim-evidence-manifest',
  })));
}

function convertWaiverRef(ref, claimId, overrideIndexes, index) {
  const id = maybeString(ref?.id) || `${claimId}:waiver:${index}`;
  const override = overrideIndexes.byId.get(id) ?? ensureArray(overrideIndexes.byClaim.get(claimId))[0];
  return {
    id,
    temporaryOverridePath: override?.path || `artifacts/assurance/temporary-overrides/${id}.json`,
    status: maybeString(override?.payload?.status) || maybeString(ref?.status) || 'unknown',
    owner: maybeString(override?.payload?.owner) || maybeString(ref?.owner) || 'unknown-owner',
    expires: maybeString(override?.payload?.expires) || maybeString(ref?.expires) || '2099-12-31',
    reason: maybeString(override?.payload?.reason) || maybeString(ref?.reason) || `Waiver linked to ${claimId}.`,
  };
}

function convertWaiverRefs(claim, overrideIndexes) {
  const refs = ensureArray(claim.waiverRefs).map((ref, index) => convertWaiverRef(ref, claim.id, overrideIndexes, index));
  for (const override of ensureArray(overrideIndexes.byClaim.get(claim.id))) {
    const id = maybeString(override.payload?.id);
    if (id && !refs.some((ref) => ref.id === id)) {
      refs.push(convertWaiverRef({ id }, claim.id, overrideIndexes, refs.length));
    }
  }
  return uniqueById(refs);
}

function convertAssumptions(claim) {
  const assumptions = [];
  for (const ref of ensureArray(claim.assumptionHandlingRefs)) {
    const mode = maybeString(ref?.mode);
    assumptions.push({
      id: maybeString(ref?.id) || `${claim.id}:assumption:${assumptions.length}`,
      statement: maybeString(ref?.reason) || `Assumption handling for ${claim.id}.`,
      status: mode === 'assumption-validation-required' ? 'needs-validation' : 'residual-risk',
      ...(maybeString(ref?.artifactPath) ? { artifactPath: normalizeArtifactPath(ref.artifactPath, 'assumption artifact path') } : {}),
    });
  }
  return uniqueById(assumptions);
}

function convertRuntimeControls(claim, state, changePackage) {
  const controls = [];
  const runtimeEvidence = ensureArray(claim.evidenceRefs).filter((ref) => normalizeEvidenceKind(ref?.kind) === 'runtime');
  for (const ref of runtimeEvidence) {
    controls.push({
      id: maybeString(ref.id) || `${claim.id}:runtime:${controls.length}`,
      kind: 'runtime-conformance',
      description: maybeString(ref.description) || `Runtime evidence linked for ${claim.id}.`,
      artifactPath: normalizeArtifactPath(ref.artifactPath || `artifacts/runtime/${claim.id}.json`, 'runtime evidence path'),
    });
  }
  if (state === 'runtime-mitigated') {
    for (const alert of ensureArray(changePackage.payload?.runtimeControls?.alerts).map(maybeString).filter(Boolean)) {
      controls.push({
        id: `alert:${alert}`,
        kind: 'alert',
        description: `Runtime alert control ${alert} is linked from change-package/v2.`,
      });
    }
    for (const featureFlag of ensureArray(changePackage.payload?.runtimeControls?.featureFlags).map(maybeString).filter(Boolean)) {
      controls.push({
        id: `feature-flag:${featureFlag}`,
        kind: 'feature-flag',
        description: `Runtime feature flag ${featureFlag} is linked from change-package/v2.`,
      });
    }
    if (controls.length === 0) {
      controls.push({
        id: `${claim.id}:runtime-control`,
        kind: 'other',
        description: `Runtime mitigation is recorded for ${claim.id}; no dedicated runtime-control artifact was linked.`,
      });
    }
  }
  return uniqueById(controls);
}

function hasEvidenceKind(claim, kind) {
  return ensureArray(claim.evidenceRefs).some((ref) => normalizeEvidenceKind(ref?.kind) === kind);
}

function hasDischargedProof(claim) {
  return ensureArray(claim.proofObligationRefs).some((ref) => maybeString(ref?.status) === 'discharged');
}

function inferState({ claim, policyClaim, changeClaim, notApplicable }) {
  if (notApplicable) return 'not-applicable';
  const policyResult = normalizeDecisionResult(policyClaim?.result, '');
  if (policyResult === 'block') return 'failed';
  if (policyResult === 'waived' || maybeString(claim.status) === 'waived') return 'waived';

  const changeStatus = maybeString(changeClaim?.status);
  if (CHANGE_PACKAGE_STATES.has(changeStatus)) return changeStatus;

  if (maybeString(claim.status) === 'unresolved') return 'unresolved';
  if (hasEvidenceKind(claim, 'runtime')) return 'runtime-mitigated';
  if (hasEvidenceKind(claim, 'proof') || hasDischargedProof(claim)) return 'proved';
  if (hasEvidenceKind(claim, 'model')) return 'model-checked';
  if (hasEvidenceKind(claim, 'behavior')) return 'tested';
  if (maybeString(claim.status) === 'satisfied') return 'satisfied';
  return 'unresolved';
}

function rationaleForState(state, claim, policyClaim, notApplicable) {
  if (state === 'not-applicable') return `Explicit applicability record: ${notApplicable.reason}`;
  if (state === 'failed') return maybeString(policyClaim?.result) === 'block'
    ? 'Policy gate marked this claim as block; failed evidence remains decision-relevant.'
    : 'Failed evidence is linked to this claim.';
  if (state === 'waived') return 'Active or recorded waiver keeps this claim distinct from satisfied claims.';
  if (state === 'runtime-mitigated') return 'Runtime controls or runtime evidence mitigate the claim without promoting it to proof.';
  if (state === 'unresolved') return 'Required evidence is missing or the current primary status is unresolved.';
  if (state === 'proved') return 'Proof-level evidence or discharged proof obligation is linked.';
  if (state === 'model-checked') return 'Model-checking evidence is linked for the stated scope.';
  if (state === 'tested') return 'Behavior test evidence is linked but no stronger model/proof evidence is claimed.';
  return 'Required evidence is linked and no stronger specialized state is claimed.';
}

function deriveDecision({ state, policyAssurance, policyClaim, evidenceRefs, missingEvidenceRefs, waiverRefs }) {
  const policyMode = normalizeDecisionMode(policyAssurance?.mode, 'report-only');
  let result = normalizeDecisionResult(policyClaim?.result, '');
  if (!result) {
    if (state === 'failed') result = 'block';
    else if (state === 'waived') result = 'waived';
    else if (['satisfied', 'tested', 'model-checked', 'proved'].includes(state)) result = 'pass';
    else result = 'report-only';
  }
  // policy-gate can report per-claim blocks during a report-only rollout. Keep those
  // visible as failed evidence, but do not promote them into enforced release blocks.
  if (policyMode === 'report-only' && result === 'block') {
    result = 'report-only';
  }
  const mode = result === 'block' ? 'strict' : policyMode;
  const enforced = mode === 'strict';
  return {
    mode,
    result,
    enforced,
    reason: maybeString(policyClaim?.reason) || decisionReason(state, result, enforced),
    sourceArtifactId: policyAssurance || policyClaim ? 'policy-gate-summary' : 'claim-level-summary',
    evidenceRefs: evidenceRefs.map((ref) => ref.id).filter((id) => ensureArray(policyClaim?.evidenceRefs).length === 0 || ensureArray(policyClaim?.evidenceRefs).includes(id)),
    missingEvidenceRefs: missingEvidenceRefs.map((ref) => ref.id).filter((id) => ensureArray(policyClaim?.missingEvidenceRefs).length === 0 || ensureArray(policyClaim?.missingEvidenceRefs).includes(id)),
    waiverRefs: waiverRefs.map((ref) => ref.id).filter((id) => ensureArray(policyClaim?.waiverRefs).length === 0 || ensureArray(policyClaim?.waiverRefs).includes(id)),
  };
}

function decisionReason(state, result, enforced) {
  if (result === 'block') return 'Strict policy blocks the claim until failed or missing evidence is resolved.';
  if (result === 'waived') return 'Policy gate recognizes an explicit waiver for this claim.';
  if (result === 'pass') return enforced ? 'Strict policy accepts linked evidence for this claim.' : 'Linked evidence is sufficient for report-only pass projection.';
  if (state === 'not-applicable') return 'Claim is explicitly outside the current applicability scope.';
  return 'Claim remains report-only until required evidence is complete or policy enforcement is enabled.';
}

function buildSource({ options, policyGateSummary, changePackage }) {
  const changeSource = changePackage.payload?.source && typeof changePackage.payload.source === 'object'
    ? changePackage.payload.source
    : {};
  return {
    repository: options.repository ?? policyGateSummary.payload?.repository ?? changeSource.repository ?? null,
    ...(options.prNumber ?? policyGateSummary.payload?.prNumber ?? changeSource.prNumber
      ? { prNumber: options.prNumber ?? policyGateSummary.payload?.prNumber ?? changeSource.prNumber }
      : {}),
    baseRef: options.baseRef ?? changeSource.baseRef ?? process.env.GITHUB_BASE_REF ?? 'unknown-base',
    headRef: options.headRef ?? changeSource.headRef ?? process.env.GITHUB_HEAD_REF ?? 'unknown-head',
    ...(options.headSha ?? process.env.GITHUB_SHA ? { headSha: options.headSha ?? process.env.GITHUB_SHA } : {}),
  };
}

function buildClaimSummary({ claim, policyClaim, changeClaim, changePackage, overrideIndexes }) {
  const notApplicable = parseNotApplicableMarker(claim);
  const state = inferState({ claim, policyClaim, changeClaim, notApplicable });
  if (!CLAIM_STATES.has(state)) throw new Error(`Unsupported claim state inferred for ${claim.id}: ${state}`);
  const evidenceRefs = convertEvidenceRefs(claim, state, policyClaim);
  const missingEvidenceRefs = convertMissingEvidenceRefs(claim);
  const waiverRefs = convertWaiverRefs(claim, overrideIndexes);
  const assumptions = convertAssumptions(claim);
  const runtimeControls = convertRuntimeControls(claim, state, changePackage);
  const decision = deriveDecision({
    state,
    policyAssurance: changePackage.policyAssurance,
    policyClaim,
    evidenceRefs,
    missingEvidenceRefs,
    waiverRefs,
  });

  return {
    claimId: maybeString(claim.id),
    statement: maybeString(claim.statement) || `Claim ${claim.id}`,
    criticality: normalizeCriticality(claim.criticality),
    targetLevel: normalizeLevel(claim.targetLevel, 'A0'),
    achievedLevel: normalizeLevel(claim.achievedLevel, normalizeLevel(claim.targetLevel, 'A0')),
    state,
    stateRationale: rationaleForState(state, claim, policyClaim, notApplicable),
    decision,
    evidenceRefs,
    missingEvidenceRefs,
    waiverRefs,
    assumptions,
    runtimeControls,
    ...(notApplicable ? { applicability: notApplicable } : {}),
    notes: Array.from(new Set(ensureArray(claim.notes).map(maybeString).filter(Boolean))).sort(compareString),
  };
}

function summarizeClaims(claims) {
  return {
    totalClaims: claims.length,
    satisfied: claims.filter((claim) => claim.state === 'satisfied').length,
    tested: claims.filter((claim) => claim.state === 'tested').length,
    modelChecked: claims.filter((claim) => claim.state === 'model-checked').length,
    proved: claims.filter((claim) => claim.state === 'proved').length,
    runtimeMitigated: claims.filter((claim) => claim.state === 'runtime-mitigated').length,
    waived: claims.filter((claim) => claim.state === 'waived').length,
    unresolved: claims.filter((claim) => claim.state === 'unresolved').length,
    failed: claims.filter((claim) => claim.state === 'failed').length,
    notApplicable: claims.filter((claim) => claim.state === 'not-applicable').length,
    enforcedDecisions: claims.filter((claim) => claim.decision.enforced).length,
    reportOnlyDecisions: claims.filter((claim) => claim.decision.mode === 'report-only').length,
  };
}

export function buildClaimLevelSummary(options) {
  const claimEvidenceManifest = resolveRequiredArtifact(options.claimEvidenceManifest, 'Claim evidence manifest');
  const policyGateSummary = resolveOptionalArtifact(options.policyGateSummary);
  const changePackage = resolveOptionalArtifact(options.changePackage);
  const temporaryOverrides = readTemporaryOverrides(options.temporaryOverrides);
  const overrideIndexes = buildOverrideIndexes(temporaryOverrides);
  const policyClaimMap = buildPolicyClaimMap(policyGateSummary);
  const changeClaimMap = buildChangeClaimMap(changePackage);
  const proofObligationsByClaim = buildProofObligationsByClaim(changePackage);
  const counterexamplesByClaim = buildCounterexamplesByClaim(changePackage);
  const policyAssurance = policyGateSummary.payload?.evaluation?.assurance ?? null;
  changePackage.policyAssurance = policyAssurance;

  const claims = ensureArray(claimEvidenceManifest.payload?.claims)
    .map((claim) => {
      const claimId = maybeString(claim.id);
      const enrichedClaim = {
        ...claim,
        proofObligationRefs: [
          ...ensureArray(claim.proofObligationRefs),
          ...ensureArray(proofObligationsByClaim.get(claimId)).map((obligation, index) => ({
            id: maybeString(obligation.id) || `${claimId}:proof:${index}`,
            status: maybeString(obligation.status) === 'discharged' ? 'discharged' : maybeString(obligation.status) || 'open',
            sourceArtifactId: 'change-package-v2',
            artifactPath: ensureArray(obligation.artifactRefs).map(maybeString).filter(Boolean)[0],
            method: maybeString(obligation.method) || 'other',
            description: `change-package/v2 proof obligation ${maybeString(obligation.id) || index}`,
          })),
        ],
        evidenceRefs: [
          ...ensureArray(claim.evidenceRefs),
          ...ensureArray(counterexamplesByClaim.get(claimId)).map((counterexample, index) => ({
            id: `change-package-v2:${claimId}:counterexample:${index}`,
            kind: 'adversarial',
            status: maybeString(counterexample.status) || 'open',
            artifactPath: maybeString(counterexample.artifactPath) || `artifacts/assurance/${claimId}/counterexample-${index}.json`,
            sourceArtifactId: 'change-package-v2',
            description: `Counterexample status=${maybeString(counterexample.status) || 'unknown'}.`,
          })),
        ],
      };
      return buildClaimSummary({
        claim: enrichedClaim,
        policyClaim: policyClaimMap.get(claimId),
        changeClaim: changeClaimMap.get(claimId),
        changePackage,
        overrideIndexes,
      });
    })
    .sort((left, right) => compareString(left.claimId, right.claimId));

  return {
    schemaVersion: SCHEMA_VERSION,
    generatedAt: options.generatedAt ? ensureDateTime(options.generatedAt) : new Date().toISOString(),
    source: buildSource({ options, policyGateSummary, changePackage }),
    inputs: {
      claimEvidenceManifest: asInputArtifact(claimEvidenceManifest, true),
      policyGateSummary: asInputArtifact(policyGateSummary, false),
      temporaryOverrides: temporaryOverrides.map((override) => ({
        path: override.path,
        schemaVersion: schemaVersionOf(override.payload),
        present: true,
        required: false,
      })),
      changePackageV2: asInputArtifact(changePackage, false),
    },
    summary: summarizeClaims(claims),
    claims,
  };
}

function loadSchemaValidator(schemaPath) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(readJson(path.resolve(schemaPath)));
}

export function validateClaimLevelSummary(summary, schemaPath = DEFAULT_SCHEMA) {
  const validate = loadSchemaValidator(schemaPath);
  if (!validate(summary)) {
    throw new Error(`claim-level summary schema validation failed: ${JSON.stringify(validate.errors ?? [], null, 2)}`);
  }
}

export function renderClaimLevelSummaryMarkdown(summary) {
  const lines = [];
  lines.push('# Claim-Level Assurance Summary');
  lines.push('');
  lines.push(`- schemaVersion: \`${summary.schemaVersion}\``);
  lines.push(`- generatedAt: \`${summary.generatedAt}\``);
  lines.push(`- source: \`${summary.source.repository ?? 'n/a'}\` ${summary.source.prNumber ? `PR #${summary.source.prNumber}` : ''}`.trim());
  lines.push(`- refs: \`${summary.source.baseRef}\` → \`${summary.source.headRef}\``);
  lines.push('');
  lines.push('## Counts');
  lines.push('');
  lines.push('| total | satisfied | tested | model-checked | proved | runtime-mitigated | waived | unresolved | failed | not-applicable | enforced | report-only |');
  lines.push('| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |');
  lines.push(`| ${summary.summary.totalClaims} | ${summary.summary.satisfied} | ${summary.summary.tested} | ${summary.summary.modelChecked} | ${summary.summary.proved} | ${summary.summary.runtimeMitigated} | ${summary.summary.waived} | ${summary.summary.unresolved} | ${summary.summary.failed} | ${summary.summary.notApplicable} | ${summary.summary.enforcedDecisions} | ${summary.summary.reportOnlyDecisions} |`);
  lines.push('');
  lines.push('## Claims');
  lines.push('');
  lines.push('| claim | state | target | achieved | decision | evidence | missing | waivers |');
  lines.push('| --- | --- | --- | --- | --- | ---: | ---: | ---: |');
  for (const claim of summary.claims) {
    lines.push(`| \`${claim.claimId}\` | ${claim.state} | ${claim.targetLevel} | ${claim.achievedLevel} | ${claim.decision.mode}/${claim.decision.result} | ${claim.evidenceRefs.length} | ${claim.missingEvidenceRefs.length} | ${claim.waiverRefs.length} |`);
  }

  const missingClaims = summary.claims.filter((claim) => claim.missingEvidenceRefs.length > 0);
  if (missingClaims.length > 0) {
    lines.push('');
    lines.push('## Missing evidence');
    for (const claim of missingClaims) {
      lines.push(`- \`${claim.claimId}\``);
      for (const missing of claim.missingEvidenceRefs) {
        lines.push(`  - ${missing.expectedKind}: ${missing.reason} (\`${missing.id}\`)`);
      }
    }
  }

  const waivedClaims = summary.claims.filter((claim) => claim.waiverRefs.length > 0);
  if (waivedClaims.length > 0) {
    lines.push('');
    lines.push('## Waivers / overrides');
    for (const claim of waivedClaims) {
      for (const waiver of claim.waiverRefs) {
        lines.push(`- \`${claim.claimId}\`: ${waiver.status}, expires ${waiver.expires}, owner ${waiver.owner} (\`${waiver.id}\`)`);
      }
    }
  }

  const notApplicableClaims = summary.claims.filter((claim) => claim.state === 'not-applicable');
  if (notApplicableClaims.length > 0) {
    lines.push('');
    lines.push('## Applicability exclusions');
    for (const claim of notApplicableClaims) {
      lines.push(`- \`${claim.claimId}\`: ${claim.applicability.reason} (scope: ${claim.applicability.scope})`);
    }
  }

  lines.push('');
  return `${lines.join('\n')}\n`;
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    usage();
    return 0;
  }
  const summary = buildClaimLevelSummary(options);
  if (options.validate) {
    validateClaimLevelSummary(summary, options.schema);
  }
  writeJson(options.outputJson, summary);
  writeText(options.outputMd, renderClaimLevelSummaryMarkdown(summary));
  process.stdout.write(`[claim-level-summary] wrote ${options.outputJson}\n`);
  process.stdout.write(`[claim-level-summary] wrote ${options.outputMd}\n`);
  return 0;
}

if (process.argv[1] && import.meta.url === `file://${path.resolve(process.argv[1])}`) {
  try {
    process.exitCode = run(process.argv.slice(2));
  } catch (error) {
    process.stderr.write(`[claim-level-summary] ${error.message}\n`);
    process.exitCode = 1;
  }
}
