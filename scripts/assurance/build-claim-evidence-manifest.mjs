#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { validateClaimEvidenceManifestSemantics } from '../ci/lib/claim-evidence-manifest-contract.mjs';

export const DEFAULT_OUTPUT_JSON = 'artifacts/assurance/claim-evidence-manifest.json';
export const DEFAULT_OUTPUT_MD = 'artifacts/assurance/claim-evidence-manifest.md';
export const DEFAULT_ASSURANCE_SUMMARY = 'artifacts/assurance/assurance-summary.json';
export const DEFAULT_VERIFY_LITE_SUMMARY = 'artifacts/verify-lite/verify-lite-run-summary.json';
export const DEFAULT_QUALITY_SCORECARD = 'artifacts/quality/quality-scorecard.json';
export const DEFAULT_CHANGE_PACKAGE_V2 = 'artifacts/change-package/change-package-v2.json';
export const DEFAULT_SCHEMA = 'schema/claim-evidence-manifest.schema.json';

const SCHEMA_VERSION = 'claim-evidence-manifest/v1';
const LEVELS = ['A0', 'A1', 'A2', 'A3', 'A4'];
const CRITICALITIES = new Set(['low', 'medium', 'high', 'critical']);
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
const PROOF_METHODS = new Set(['spec', 'property', 'tla', 'alloy', 'smt', 'csp', 'lean', 'kani', 'runtime', 'manual', 'other']);
const PROOF_STATUSES = new Set(['open', 'discharged', 'waived', 'unresolved']);

function usage() {
  process.stdout.write(`Usage: node scripts/assurance/build-claim-evidence-manifest.mjs [options]\n\nOptions:\n  --assurance-summary <path>       assurance-summary/v1 input (default: ${DEFAULT_ASSURANCE_SUMMARY})\n  --change-package <path>          optional change-package/v2 input (default probe: ${DEFAULT_CHANGE_PACKAGE_V2})\n  --quality-scorecard <path>       optional quality-scorecard/v1 input (default: ${DEFAULT_QUALITY_SCORECARD})\n  --verify-lite-summary <path>     optional verify-lite summary input (default: ${DEFAULT_VERIFY_LITE_SUMMARY})\n  --trace-bundle <path>            optional trace bundle input; first present path is used\n  --output-json <path>             output JSON path (default: ${DEFAULT_OUTPUT_JSON})\n  --output-md <path>               output Markdown path (default: ${DEFAULT_OUTPUT_MD})\n  --schema <path>                  schema used for output validation (default: ${DEFAULT_SCHEMA})\n  --generated-at <iso-date-time>   override generatedAt for deterministic tests\n  --no-validate                    skip schema and semantic validation before writing\n  --help                           show this help\n`);
}

function readRequiredValue(argv, index, option) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`${option} requires a value`);
  }
  return next;
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    assuranceSummary: DEFAULT_ASSURANCE_SUMMARY,
    changePackages: [],
    qualityScorecard: DEFAULT_QUALITY_SCORECARD,
    verifyLiteSummary: DEFAULT_VERIFY_LITE_SUMMARY,
    traceBundles: [],
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    schema: DEFAULT_SCHEMA,
    generatedAt: null,
    validate: true,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--assurance-summary') {
      options.assuranceSummary = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--change-package') {
      if (options.changePackages.length > 0) {
        throw new Error('--change-package can only be provided once');
      }
      options.changePackages.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--quality-scorecard') {
      options.qualityScorecard = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--verify-lite-summary') {
      options.verifyLiteSummary = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--trace-bundle') {
      options.traceBundles.push(readRequiredValue(argv, index, arg));
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
    if (arg === '--no-validate') {
      options.validate = false;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  return options;
}

function readJson(targetPath) {
  return JSON.parse(fs.readFileSync(targetPath, 'utf8'));
}

function existsFile(targetPath) {
  return Boolean(targetPath) && fs.existsSync(targetPath) && fs.statSync(targetPath).isFile();
}

function resolveRequiredArtifact(inputPath, label) {
  const resolvedPath = path.resolve(inputPath);
  if (!existsFile(resolvedPath)) {
    throw new Error(`${label} not found at ${resolvedPath}`);
  }
  return {
    path: inputPath,
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
    path: inputPath,
    present: true,
    payload: readJson(resolvedPath),
  };
}

function firstPresentArtifact(paths) {
  for (const candidate of paths) {
    const artifact = resolveOptionalArtifact(candidate);
    if (artifact.present) {
      return artifact;
    }
  }
  return { path: null, present: false, payload: null };
}

function defaultTraceBundleCandidates() {
  const directories = ['artifacts/trace', 'artifacts/observability'];
  const candidates = [];
  for (const directory of directories) {
    if (!fs.existsSync(directory) || !fs.statSync(directory).isDirectory()) {
      continue;
    }
    for (const entry of fs.readdirSync(directory).sort((left, right) => left.localeCompare(right))) {
      if (/trace-bundle.*\.json$/u.test(entry) || /.*trace-bundle\.json$/u.test(entry)) {
        candidates.push(path.join(directory, entry));
      }
    }
  }
  return candidates;
}

function levelIndex(level) {
  const index = LEVELS.indexOf(level);
  return index >= 0 ? index : 0;
}

function normalizeLevel(value, fallback = 'A0') {
  const candidate = typeof value === 'string' ? value.trim() : '';
  return LEVELS.includes(candidate) ? candidate : fallback;
}

function maxLevel(left, right) {
  return LEVELS[Math.max(levelIndex(normalizeLevel(left)), levelIndex(normalizeLevel(right)))];
}

function minLevel(left, right) {
  return LEVELS[Math.min(levelIndex(normalizeLevel(left)), levelIndex(normalizeLevel(right)))];
}

function decrementLevel(level) {
  return LEVELS[Math.max(0, levelIndex(normalizeLevel(level)) - 1)];
}

function normalizeCriticality(value) {
  const candidate = typeof value === 'string' ? value.trim().toLowerCase() : '';
  return CRITICALITIES.has(candidate) ? candidate : 'medium';
}

function sanitizeId(value) {
  return String(value ?? 'unknown')
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9_.:-]+/gu, '-')
    .replace(/^-+|-+$/gu, '')
    || 'unknown';
}

function ensureArray(value) {
  return Array.isArray(value) ? value : [];
}

function ensureObject(value) {
  return value && typeof value === 'object' && !Array.isArray(value) ? value : {};
}

function schemaVersionOf(payload) {
  return typeof payload?.schemaVersion === 'string' && payload.schemaVersion.trim()
    ? payload.schemaVersion.trim()
    : null;
}

function buildSourceArtifact({ id, kind, artifact, required, description }) {
  return {
    id,
    kind,
    path: artifact.present ? artifact.path : null,
    present: artifact.present,
    required,
    schemaVersion: artifact.present ? schemaVersionOf(artifact.payload) : null,
    description,
  };
}

function isChangePackageV2(artifact) {
  return artifact.present && schemaVersionOf(artifact.payload) === 'change-package/v2';
}

function resolveChangePackageV2(paths) {
  const candidates = paths.length > 0 ? paths : [DEFAULT_CHANGE_PACKAGE_V2];
  for (const candidate of candidates) {
    const artifact = resolveOptionalArtifact(candidate);
    if (isChangePackageV2(artifact)) {
      return artifact;
    }
  }
  return { path: null, present: false, payload: null };
}

function resolveTraceBundle(paths) {
  const candidates = paths.length > 0 ? paths : defaultTraceBundleCandidates();
  return firstPresentArtifact(candidates);
}

function compareStatusPriority(status) {
  switch (status) {
    case 'unresolved':
      return 4;
    case 'waived':
      return 3;
    case 'partial':
      return 2;
    case 'satisfied':
      return 1;
    default:
      return 0;
  }
}

function combineStatus(currentStatus, nextStatus) {
  if (!currentStatus) {
    return nextStatus;
  }
  if (!nextStatus) {
    return currentStatus;
  }
  return compareStatusPriority(nextStatus) > compareStatusPriority(currentStatus) ? nextStatus : currentStatus;
}

function mapLaneToEvidenceKind(lane) {
  switch (String(lane ?? '').toLowerCase()) {
    case 'spec':
      return 'spec';
    case 'behavior':
      return 'behavior';
    case 'adversarial':
      return 'adversarial';
    case 'model':
      return 'model';
    case 'proof':
      return 'proof';
    case 'runtime':
      return 'runtime';
    default:
      return 'other';
  }
}

function inferEvidenceKindFromText(text, fallback = 'other') {
  const value = String(text ?? '').toLowerCase();
  if (/quality|scorecard/u.test(value)) return 'quality';
  if (/trace|otel|observability/u.test(value)) return 'trace';
  if (/policy|rego|gate/u.test(value)) return 'policy';
  if (/runtime|alert|feature-?flag|control/u.test(value)) return 'runtime';
  if (/tla|alloy|smt|csp|lean|kani|proof|formal/u.test(value)) return 'proof';
  if (/property|test|scenario|bdd|gwt/u.test(value)) return 'behavior';
  if (/conformance|model/u.test(value)) return 'model';
  if (/counterexample|adversarial/u.test(value)) return 'adversarial';
  if (/schema|spec|context-pack|product-coproduct/u.test(value)) return 'spec';
  return fallback;
}

function normalizeEvidenceKind(value, fallback = 'other') {
  const candidate = String(value ?? '').trim().toLowerCase();
  return EVIDENCE_KINDS.has(candidate) ? candidate : inferEvidenceKindFromText(candidate, fallback);
}

function mapAssuranceStatus(value, missingCount) {
  if (value === 'satisfied') return 'satisfied';
  if (value === 'waived') return 'waived';
  if (value === 'unresolved') return 'unresolved';
  if (value === 'partial' || value === 'warning') return 'partial';
  return missingCount > 0 ? 'partial' : 'unresolved';
}

function mapChangeClaimStatus(claimStatus, assuranceStatus, targetLevel, achievedLevel) {
  if (claimStatus === 'waived' || assuranceStatus === 'waived') return 'waived';
  if (claimStatus === 'unresolved' || assuranceStatus === 'unresolved' || assuranceStatus === 'unassessed') return 'unresolved';
  if (assuranceStatus === 'partial') return 'partial';
  if (assuranceStatus === 'satisfied') return 'satisfied';
  return levelIndex(achievedLevel) >= levelIndex(targetLevel) ? 'satisfied' : 'partial';
}

function normalizeProofStatus(value) {
  const candidate = String(value ?? '').trim().toLowerCase();
  return PROOF_STATUSES.has(candidate) ? candidate : 'unresolved';
}

function normalizeProofMethod(value) {
  const candidate = String(value ?? '').trim().toLowerCase();
  return PROOF_METHODS.has(candidate) ? candidate : 'other';
}

function artifactPathWithPointer(basePath, pointer) {
  return `${basePath}#${pointer}`;
}

function getOrCreateClaim(claimsById, id, defaults = {}) {
  const claimId = sanitizeId(id);
  if (!claimsById.has(claimId)) {
    claimsById.set(claimId, {
      id: claimId,
      statement: defaults.statement || `Claim ${claimId}`,
      criticality: normalizeCriticality(defaults.criticality),
      targetLevel: normalizeLevel(defaults.targetLevel, 'A0'),
      achievedLevel: normalizeLevel(defaults.achievedLevel, 'A0'),
      status: defaults.status || 'unresolved',
      evidenceRefs: [],
      proofObligationRefs: [],
      missingEvidenceRefs: [],
      waiverRefs: [],
      notes: [],
    });
  }
  const claim = claimsById.get(claimId);
  if (defaults.statement && claim.statement.startsWith('Claim ')) {
    claim.statement = defaults.statement;
  }
  if (defaults.criticality) {
    claim.criticality = normalizeCriticality(defaults.criticality);
  }
  if (defaults.targetLevel) {
    claim.targetLevel = maxLevel(claim.targetLevel, defaults.targetLevel);
  }
  if (defaults.achievedLevel) {
    claim.achievedLevel = maxLevel(claim.achievedLevel, defaults.achievedLevel);
  }
  if (defaults.status) {
    claim.status = combineStatus(claim.status, defaults.status);
  }
  return claim;
}

function getReferencedClaim(claimsById, rawClaimId, context) {
  const claimId = sanitizeId(rawClaimId);
  const claim = claimsById.get(claimId);
  if (!claim) {
    throw new Error(`${context} references unknown claim '${String(rawClaimId)}'`);
  }
  return claim;
}

function pushUniqueById(items, nextItem) {
  if (!nextItem || !nextItem.id) {
    return;
  }
  if (items.some((item) => item.id === nextItem.id)) {
    return;
  }
  items.push(nextItem);
}

function pushNote(claim, note) {
  const value = String(note ?? '').trim();
  if (!value || claim.notes.includes(value)) {
    return;
  }
  claim.notes.push(value);
}

function addMissingEvidence(claim, { id, expectedKind, reason, sourceArtifactId }) {
  const item = {
    id: sanitizeId(id),
    expectedKind: normalizeEvidenceKind(expectedKind),
    reason: String(reason || 'Evidence required for the target assurance level.'),
  };
  if (sourceArtifactId) {
    item.sourceArtifactId = sourceArtifactId;
  }
  pushUniqueById(claim.missingEvidenceRefs, item);
}

function ingestAssuranceSummary(claimsById, artifact) {
  const sourceArtifactId = 'assurance-summary';
  const payload = ensureObject(artifact.payload);
  const warningsByClaimId = new Map();
  for (const warning of ensureArray(payload.warnings)) {
    const warningClaimId = warning?.claimId;
    if (!warningClaimId) {
      continue;
    }
    const key = String(warningClaimId);
    if (!warningsByClaimId.has(key)) {
      warningsByClaimId.set(key, []);
    }
    warningsByClaimId.get(key).push(warning);
  }

  for (const [claimIndex, rawClaim] of ensureArray(payload.claims).entries()) {
    const claimId = rawClaim?.claimId ?? rawClaim?.id;
    if (!claimId) {
      continue;
    }
    const missingLanes = ensureArray(rawClaim.missingLanes);
    const missingEvidenceKinds = ensureArray(rawClaim.missingEvidenceKinds);
    const missingCount = missingLanes.length + missingEvidenceKinds.length;
    const targetLevel = normalizeLevel(rawClaim.targetLevel, 'A0');
    const status = mapAssuranceStatus(rawClaim.status, missingCount);
    const achievedLevel = status === 'satisfied' ? targetLevel : decrementLevel(targetLevel);
    const claim = getOrCreateClaim(claimsById, claimId, {
      statement: rawClaim.statement,
      criticality: rawClaim.criticality,
      targetLevel,
      achievedLevel,
      status,
    });
    pushNote(
      claim,
      status === 'satisfied'
        ? `achievedLevel derived from assurance-summary satisfied status at targetLevel ${targetLevel}.`
        : `achievedLevel conservatively derived below targetLevel ${targetLevel} because assurance-summary status=${rawClaim.status ?? 'unknown'}.`,
    );

    for (const [evidenceIndex, evidence] of ensureArray(rawClaim.evidence).entries()) {
      if (!evidence || typeof evidence !== 'object') {
        continue;
      }
      const kind = normalizeEvidenceKind(evidence.kind, mapLaneToEvidenceKind(evidence.lane));
      const artifactPath = String(evidence.artifactPath || artifact.path);
      pushUniqueById(claim.evidenceRefs, {
        id: sanitizeId(`${sourceArtifactId}:${claim.id}:${evidenceIndex}:${evidence.kind || evidence.lane || 'evidence'}`),
        kind,
        artifactPath,
        sourceArtifactId,
        description: String(evidence.detail || evidence.origin || 'Assurance summary evidence'),
      });
    }

    for (const lane of missingLanes) {
      addMissingEvidence(claim, {
        id: `${sourceArtifactId}:${claim.id}:missing-lane:${lane}`,
        expectedKind: mapLaneToEvidenceKind(lane),
        reason: `Required assurance lane '${lane}' is not linked for this claim.`,
        sourceArtifactId,
      });
    }
    for (const kind of missingEvidenceKinds) {
      addMissingEvidence(claim, {
        id: `${sourceArtifactId}:${claim.id}:missing-kind:${kind}`,
        expectedKind: normalizeEvidenceKind(kind),
        reason: `Required evidence kind '${kind}' is not linked for this claim.`,
        sourceArtifactId,
      });
    }

    const relatedWarnings = warningsByClaimId.get(String(claimId)) ?? [];
    for (const warning of relatedWarnings) {
      pushNote(claim, `assurance-warning:${warning.code ?? 'unknown'} ${warning.message ?? ''}`.trim());
    }
    if (claimIndex === 0 && payload.summary?.warningCount > 0 && relatedWarnings.length === 0) {
      pushNote(claim, `assurance-summary warningCount=${payload.summary.warningCount}`);
    }
  }
}

function addQualityScorecardEvidence(claimsById, artifact) {
  if (!artifact.present) {
    return;
  }
  const sourceArtifactId = 'quality-scorecard';
  const assuranceCoverage = artifact.payload?.dimensions?.assuranceCoverage;
  if (!assuranceCoverage || typeof assuranceCoverage !== 'object') {
    return;
  }
  for (const claim of claimsById.values()) {
    pushUniqueById(claim.evidenceRefs, {
      id: sanitizeId(`${sourceArtifactId}:assuranceCoverage:${claim.id}`),
      kind: 'quality',
      artifactPath: artifactPathWithPointer(artifact.path, '/dimensions/assuranceCoverage'),
      sourceArtifactId,
      description: String(assuranceCoverage.summary || 'Quality scorecard assurance coverage dimension'),
    });
  }
}

function addTraceEvidenceForRuntimeClaims(claimsById, artifact) {
  if (!artifact.present) {
    return;
  }
  const sourceArtifactId = 'trace-bundle';
  for (const claim of claimsById.values()) {
    const wantsRuntime = claim.missingEvidenceRefs.some((entry) => entry.expectedKind === 'runtime')
      || claim.evidenceRefs.some((entry) => entry.kind === 'runtime');
    if (!wantsRuntime) {
      continue;
    }
    pushUniqueById(claim.evidenceRefs, {
      id: sanitizeId(`${sourceArtifactId}:runtime:${claim.id}`),
      kind: 'trace',
      artifactPath: artifact.path,
      sourceArtifactId,
      description: 'Trace bundle available for runtime evidence review',
    });
  }
}

function addVerifyLiteEvidenceNotes(claimsById, artifact) {
  if (!artifact.present) {
    return;
  }
  const steps = ensureObject(artifact.payload?.steps);
  const failedSteps = Object.entries(steps)
    .filter(([, value]) => value && typeof value === 'object' && value.status && !['success', 'skipped'].includes(value.status))
    .map(([key]) => key)
    .sort((left, right) => left.localeCompare(right));
  if (failedSteps.length === 0) {
    return;
  }
  for (const claim of claimsById.values()) {
    pushNote(claim, `verify-lite non-success steps: ${failedSteps.join(', ')}`);
  }
}

function evidenceKindForChangeClaimStatus(status) {
  switch (status) {
    case 'proved':
    case 'model-checked':
      return 'proof';
    case 'tested':
      return 'behavior';
    case 'runtime-mitigated':
      return 'runtime';
    case 'waived':
      return 'manual';
    default:
      return 'other';
  }
}

function ingestChangePackageV2(claimsById, artifact) {
  if (!artifact.present) {
    return;
  }
  const sourceArtifactId = 'change-package-v2';
  const payload = ensureObject(artifact.payload);
  const assurance = ensureObject(payload.assurance);
  const targetLevel = normalizeLevel(assurance.targetLevel, 'A0');
  const achievedLevel = normalizeLevel(assurance.achievedLevel, decrementLevel(targetLevel));
  const assuranceStatus = String(assurance.status ?? '').trim();

  for (const [claimIndex, rawClaim] of ensureArray(payload.claims).entries()) {
    if (!rawClaim?.id) {
      continue;
    }
    const status = mapChangeClaimStatus(rawClaim.status, assuranceStatus, targetLevel, achievedLevel);
    const claim = getOrCreateClaim(claimsById, rawClaim.id, {
      statement: rawClaim.statement,
      criticality: rawClaim.criticality,
      targetLevel,
      achievedLevel,
      status,
    });
    claim.achievedLevel = achievedLevel;
    pushNote(
      claim,
      `achievedLevel imported from change-package/v2 top-level assurance: targetLevel=${targetLevel}, achievedLevel=${achievedLevel}, status=${assuranceStatus || 'unknown'}.`,
    );

    pushUniqueById(claim.evidenceRefs, {
      id: sanitizeId(`${sourceArtifactId}:${claim.id}`),
      kind: evidenceKindForChangeClaimStatus(rawClaim.status),
      artifactPath: artifactPathWithPointer(artifact.path, `/claims/${claimIndex}`),
      sourceArtifactId,
      description: `Change-package v2 claim anchor is present (status=${rawClaim.status ?? 'unknown'}).`,
    });

    for (const [artifactIndex, artifactRef] of ensureArray(rawClaim.artifactRefs).entries()) {
      pushUniqueById(claim.evidenceRefs, {
        id: sanitizeId(`${sourceArtifactId}:${claim.id}:artifact:${artifactIndex}`),
        kind: inferEvidenceKindFromText(artifactRef, evidenceKindForChangeClaimStatus(rawClaim.status)),
        artifactPath: String(artifactRef),
        sourceArtifactId,
        description: 'Change-package v2 artifactRef linked to claim',
      });
    }
  }

  for (const [obligationIndex, obligation] of ensureArray(payload.proofObligations).entries()) {
    if (!obligation?.claimId || !obligation?.id) {
      continue;
    }
    const claim = getReferencedClaim(
      claimsById,
      obligation.claimId,
      `change-package/v2 proofObligations[${obligationIndex}].claimId`,
    );
    const status = normalizeProofStatus(obligation.status);
    if (status === 'open') {
      claim.status = combineStatus(claim.status, 'partial');
      claim.achievedLevel = minLevel(claim.achievedLevel, achievedLevel);
    }
    pushUniqueById(claim.proofObligationRefs, {
      id: sanitizeId(obligation.id),
      status,
      sourceArtifactId,
      artifactPath: ensureArray(obligation.artifactRefs)[0] || artifactPathWithPointer(artifact.path, `/proofObligations/${obligationIndex}`),
      method: normalizeProofMethod(obligation.method),
      description: `Change-package v2 proof obligation status=${status}`,
    });
    if (status === 'open' || status === 'unresolved') {
      addMissingEvidence(claim, {
        id: `${sourceArtifactId}:${claim.id}:proof-obligation:${obligation.id}`,
        expectedKind: 'proof',
        reason: `Proof obligation '${obligation.id}' is ${status}.`,
        sourceArtifactId,
      });
    }
  }

  for (const [counterexampleIndex, counterexample] of ensureArray(payload.counterexamples).entries()) {
    for (const rawClaimId of ensureArray(counterexample?.claimIds)) {
      const claim = getReferencedClaim(
        claimsById,
        rawClaimId,
        `change-package/v2 counterexamples[${counterexampleIndex}].claimIds`,
      );
      const counterexampleStatus = String(counterexample?.status ?? '').trim();
      if (counterexampleStatus === 'resolved' || counterexampleStatus === 'accepted-risk') {
        pushUniqueById(claim.evidenceRefs, {
          id: sanitizeId(`${sourceArtifactId}:${claim.id}:counterexample:${counterexampleIndex}`),
          kind: 'adversarial',
          artifactPath: String(counterexample.artifactPath || artifactPathWithPointer(artifact.path, `/counterexamples/${counterexampleIndex}`)),
          sourceArtifactId,
          description: `Counterexample is ${counterexampleStatus}.`,
        });
      } else {
        claim.status = combineStatus(claim.status, 'partial');
        addMissingEvidence(claim, {
          id: `${sourceArtifactId}:${claim.id}:open-counterexample:${counterexampleIndex}`,
          expectedKind: 'adversarial',
          reason: `Counterexample is ${counterexampleStatus || 'open'}.`,
          sourceArtifactId,
        });
      }
    }
  }

  for (const [waiverIndex, waiver] of ensureArray(payload.waivers).entries()) {
    for (const rawClaimId of ensureArray(waiver?.relatedClaimIds)) {
      const claim = getReferencedClaim(
        claimsById,
        rawClaimId,
        `change-package/v2 waivers[${waiverIndex}].relatedClaimIds`,
      );
      claim.status = combineStatus(claim.status, 'waived');
      claim.targetLevel = maxLevel(claim.targetLevel, targetLevel);
      claim.achievedLevel = maxLevel(claim.achievedLevel, achievedLevel);
      pushUniqueById(claim.waiverRefs, {
        id: sanitizeId(`${sourceArtifactId}:waiver:${waiverIndex}:${claim.id}`),
        sourceArtifactId,
        status: waiverStatus(waiver?.expires),
        owner: String(waiver?.owner || 'unknown'),
        expires: waiver?.expires,
        reason: String(waiver?.reason || 'Change-package v2 waiver'),
      });
    }
  }

  for (const claim of claimsById.values()) {
    if ((claim.status === 'partial' || claim.status === 'unresolved') && claim.missingEvidenceRefs.length === 0) {
      addMissingEvidence(claim, {
        id: `${sourceArtifactId}:${claim.id}:target-${claim.targetLevel}:achieved-${claim.achievedLevel}`,
        expectedKind: 'other',
        reason: `achievedLevel ${claim.achievedLevel} is below targetLevel ${claim.targetLevel}; additional evidence is required.`,
        sourceArtifactId,
      });
    }
  }
}

function waiverStatus(expires) {
  if (typeof expires !== 'string' || !/^\d{4}-\d{2}-\d{2}$/u.test(expires)) {
    return 'unknown';
  }
  const today = new Date().toISOString().slice(0, 10);
  return expires < today ? 'expired' : 'active';
}

function normalizeFinalClaim(claim) {
  claim.evidenceRefs.sort((left, right) => left.id.localeCompare(right.id));
  claim.proofObligationRefs.sort((left, right) => left.id.localeCompare(right.id));
  claim.missingEvidenceRefs.sort((left, right) => left.id.localeCompare(right.id));
  claim.waiverRefs.sort((left, right) => left.id.localeCompare(right.id));
  claim.notes.sort((left, right) => left.localeCompare(right));

  if (claim.status === 'waived' && claim.waiverRefs.length === 0) {
    claim.status = 'partial';
    addMissingEvidence(claim, {
      id: `${claim.id}:waiver-reference-required`,
      expectedKind: 'manual',
      reason: 'A waived claim requires an explicit waiver reference.',
    });
  }
  if (claim.status === 'satisfied') {
    claim.achievedLevel = maxLevel(claim.achievedLevel, claim.targetLevel);
  } else if (claim.status === 'partial' && levelIndex(claim.achievedLevel) >= levelIndex(claim.targetLevel)) {
    claim.achievedLevel = decrementLevel(claim.targetLevel);
  } else if (claim.status === 'unresolved') {
    claim.achievedLevel = minLevel(claim.achievedLevel, decrementLevel(claim.targetLevel));
  }

  return claim;
}

function buildSummary(claims) {
  return {
    totalClaims: claims.length,
    fullySupported: claims.filter((claim) => claim.status === 'satisfied').length,
    partiallySupported: claims.filter((claim) => claim.status === 'partial').length,
    waived: claims.filter((claim) => claim.status === 'waived').length,
    unresolved: claims.filter((claim) => claim.status === 'unresolved').length,
  };
}

export function buildClaimEvidenceManifest(options) {
  const assuranceSummary = resolveRequiredArtifact(options.assuranceSummary, 'Assurance summary');
  const changePackage = resolveChangePackageV2(options.changePackages);
  const qualityScorecard = resolveOptionalArtifact(options.qualityScorecard);
  const verifyLiteSummary = resolveOptionalArtifact(options.verifyLiteSummary);
  const traceBundle = resolveTraceBundle(options.traceBundles);

  const sourceArtifacts = [
    buildSourceArtifact({
      id: 'assurance-summary',
      kind: 'assurance-summary',
      artifact: assuranceSummary,
      required: true,
      description: 'Lane coverage and evidence summary input',
    }),
    buildSourceArtifact({
      id: 'change-package-v2',
      kind: 'change-package-v2',
      artifact: changePackage,
      required: false,
      description: 'Optional proof-carrying change package input',
    }),
    buildSourceArtifact({
      id: 'quality-scorecard',
      kind: 'quality-scorecard',
      artifact: qualityScorecard,
      required: false,
      description: 'Quality gate evidence input',
    }),
    buildSourceArtifact({
      id: 'verify-lite-run-summary',
      kind: 'verify-lite-run-summary',
      artifact: verifyLiteSummary,
      required: false,
      description: 'Optional verify-lite run summary input',
    }),
    buildSourceArtifact({
      id: 'trace-bundle',
      kind: 'trace-bundle',
      artifact: traceBundle,
      required: false,
      description: 'Optional trace bundle input',
    }),
  ];

  const claimsById = new Map();
  ingestAssuranceSummary(claimsById, assuranceSummary);
  ingestChangePackageV2(claimsById, changePackage);
  addQualityScorecardEvidence(claimsById, qualityScorecard);
  addTraceEvidenceForRuntimeClaims(claimsById, traceBundle);
  addVerifyLiteEvidenceNotes(claimsById, verifyLiteSummary);

  const claims = Array.from(claimsById.values())
    .map(normalizeFinalClaim)
    .sort((left, right) => left.id.localeCompare(right.id));

  return {
    schemaVersion: SCHEMA_VERSION,
    generatedAt: options.generatedAt || new Date().toISOString(),
    sourceArtifacts,
    claims,
    summary: buildSummary(claims),
  };
}

function escapeMarkdown(value) {
  return String(value ?? '')
    .replace(/\\/gu, '\\\\')
    .replace(/\|/gu, '\\|')
    .replace(/\r?\n/gu, ' ')
    .trim();
}

function renderTable(headers, rows) {
  return [
    `| ${headers.map(escapeMarkdown).join(' | ')} |`,
    `| ${headers.map(() => '---').join(' | ')} |`,
    ...rows.map((row) => `| ${row.map(escapeMarkdown).join(' | ')} |`),
  ].join('\n');
}

export function renderClaimEvidenceManifestMarkdown(manifest) {
  const missingEvidence = manifest.claims.flatMap((claim) =>
    claim.missingEvidenceRefs.map((entry) => ({ claimId: claim.id, ...entry })),
  );
  const waivers = manifest.claims.flatMap((claim) => claim.waiverRefs.map((entry) => ({ claimId: claim.id, ...entry })));
  const presentSourceCount = manifest.sourceArtifacts.filter((artifact) => artifact.present).length;
  const lines = [
    '# Claim Evidence Manifest',
    '',
    `- schemaVersion: ${manifest.schemaVersion}`,
    `- generatedAt: ${manifest.generatedAt}`,
    `- sourceArtifacts: ${presentSourceCount}/${manifest.sourceArtifacts.length} present`,
    `- claims: ${manifest.summary.totalClaims} total; ${manifest.summary.fullySupported} satisfied, ${manifest.summary.partiallySupported} partial, ${manifest.summary.waived} waived, ${manifest.summary.unresolved} unresolved`,
    `- missingEvidenceRefs: ${missingEvidence.length}`,
    `- waiverRefs: ${waivers.length}`,
    '',
    '## Source artifacts',
    '',
    renderTable(
      ['id', 'kind', 'present', 'required', 'path', 'schemaVersion'],
      manifest.sourceArtifacts.map((artifact) => [
        artifact.id,
        artifact.kind,
        String(artifact.present),
        String(artifact.required),
        artifact.path ?? 'n/a',
        artifact.schemaVersion ?? 'n/a',
      ]),
    ),
    '',
    '## Claims',
    '',
    renderTable(
      ['claim', 'criticality', 'target', 'achieved', 'status', 'evidence', 'missing', 'waivers'],
      manifest.claims.map((claim) => [
        claim.id,
        claim.criticality,
        claim.targetLevel,
        claim.achievedLevel,
        claim.status,
        String(claim.evidenceRefs.length),
        String(claim.missingEvidenceRefs.length),
        String(claim.waiverRefs.length),
      ]),
    ),
    '',
    '## Missing evidence',
    '',
  ];

  if (missingEvidence.length === 0) {
    lines.push('- none');
  } else {
    for (const entry of missingEvidence) {
      lines.push(`- ${entry.claimId}: ${entry.id} (${entry.expectedKind}) — ${entry.reason}`);
    }
  }

  lines.push('', '## Waivers', '');
  if (waivers.length === 0) {
    lines.push('- none');
  } else {
    for (const entry of waivers) {
      const owner = entry.owner ? ` owner=${entry.owner}` : '';
      const expires = entry.expires ? ` expires=${entry.expires}` : '';
      lines.push(`- ${entry.claimId}: ${entry.id} status=${entry.status}${owner}${expires} — ${entry.reason ?? 'n/a'}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

export function validateManifest(manifest, schemaPath = DEFAULT_SCHEMA) {
  const schema = readJson(path.resolve(schemaPath));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  if (!validate(manifest)) {
    const details = JSON.stringify(validate.errors ?? [], null, 2);
    throw new Error(`claim-evidence-manifest schema validation failed: ${details}`);
  }
  const semanticErrors = validateClaimEvidenceManifestSemantics(manifest);
  if (semanticErrors.length > 0) {
    throw new Error(`claim-evidence-manifest semantic validation failed: ${JSON.stringify(semanticErrors, null, 2)}`);
  }
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    usage();
    return 0;
  }
  const manifest = buildClaimEvidenceManifest(options);
  if (options.validate) {
    validateManifest(manifest, options.schema);
  }
  const markdown = renderClaimEvidenceManifestMarkdown(manifest);
  const outputJsonPath = path.resolve(options.outputJson);
  const outputMdPath = path.resolve(options.outputMd);
  fs.mkdirSync(path.dirname(outputJsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(outputMdPath), { recursive: true });
  fs.writeFileSync(outputJsonPath, `${JSON.stringify(manifest, null, 2)}\n`, 'utf8');
  fs.writeFileSync(outputMdPath, markdown, 'utf8');
  process.stdout.write(`[claim-evidence-manifest] wrote ${outputJsonPath}\n`);
  process.stdout.write(`[claim-evidence-manifest] wrote ${outputMdPath}\n`);
  return 0;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  try {
    process.exitCode = run();
  } catch (error) {
    process.stderr.write(`[claim-evidence-manifest] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}
