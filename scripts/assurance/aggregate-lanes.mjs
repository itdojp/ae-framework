#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import yaml from 'yaml';
import { buildArtifactMetadata } from '../ci/lib/artifact-metadata.mjs';

const DEFAULT_OUTPUT_JSON = 'artifacts/assurance/assurance-summary.json';
const DEFAULT_OUTPUT_MD = 'artifacts/assurance/assurance-summary.md';

const LANE_ORDER = ['spec', 'behavior', 'adversarial', 'model', 'proof', 'runtime'];
const SOURCE_KINDS = new Set([
  'spec-derived',
  'source-derived',
  'model-derived',
  'runtime-derived',
  'manual',
  'unknown',
]);
const WARNING_CODES = new Set([
  'all-evidence-derived-from-source',
  'same-generator-lineage',
  'missing-spec-derived-evidence',
  'unresolved-critical-counterexample',
  'insufficient-independent-lanes',
  'context-pack-profile-mismatch',
  'unknown-claim-ref',
  'unlinked-counterexample',
  'unrecognized-evidence-claim',
  'assumption-validation-required',
]);

const SECURITY_CLAIM_TYPES = new Set(['invariant', 'precondition', 'postcondition', 'assumption']);
const ASSUMPTION_HANDLING_MODES = new Set(['assumption-validation-required', 'residual-risk']);

const usage = () => {
  console.log(`Usage: node scripts/assurance/aggregate-lanes.mjs --assurance-profile <path> [options]

Options:
  --context-pack <path>          Context Pack v1 input. Repeatable.
  --verify-lite-summary <path>   Verify Lite summary JSON.
  --formal-summary <path>        Formal summary v1/v2 JSON. Repeatable.
  --conformance-report <path>    Conformance report JSON.
  --counterexample <path>        Counterexample JSON. Repeatable.
  --evidence-manifest <path>     Supplemental evidence manifest JSON. Repeatable.
  --producer-summary <path>      Producer normalization summary JSON. Repeatable.
  --boundary-map-summary <path>  Context Pack boundary-map summary JSON. Repeatable.
  --claim-evidence-manifest <path>
                                Claim evidence manifest JSON. Repeatable.
  --policy-decision <path>       Policy decision JSON.
  --security-claims <path>       security-claim/v1 JSON input.
  --security-findings <path>     security-finding/v1 JSON input.
  --security-review <path>       security-review/v1 JSON input.
  --output-json <path>           Output JSON path (default: ${DEFAULT_OUTPUT_JSON})
  --output-md <path>             Output Markdown path (default: ${DEFAULT_OUTPUT_MD})
  --help                         Show this help.
`);
};

const readRequiredValue = (argv, index, flag) => {
  const next = argv[index + 1];
  const value = typeof next === 'string' ? next.trim() : '';
  if (!value || value.startsWith('--')) {
    throw new Error(`${flag} requires a value`);
  }
  return value;
};

export const parseArgs = (argv = process.argv.slice(2)) => {
  const options = {
    assuranceProfile: null,
    contextPacks: [],
    verifyLiteSummary: null,
    formalSummaries: [],
    conformanceReport: null,
    counterexamples: [],
    evidenceManifests: [],
    producerSummaries: [],
    boundaryMapSummaries: [],
    claimEvidenceManifests: [],
    policyDecision: null,
    securityClaims: null,
    securityFindings: null,
    securityReview: null,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    }
    if (arg === '--assurance-profile') {
      options.assuranceProfile = readRequiredValue(argv, index, '--assurance-profile');
      index += 1;
      continue;
    }
    if (arg === '--context-pack') {
      options.contextPacks.push(readRequiredValue(argv, index, '--context-pack'));
      index += 1;
      continue;
    }
    if (arg === '--verify-lite-summary') {
      options.verifyLiteSummary = readRequiredValue(argv, index, '--verify-lite-summary');
      index += 1;
      continue;
    }
    if (arg === '--formal-summary') {
      options.formalSummaries.push(readRequiredValue(argv, index, '--formal-summary'));
      index += 1;
      continue;
    }
    if (arg === '--conformance-report') {
      options.conformanceReport = readRequiredValue(argv, index, '--conformance-report');
      index += 1;
      continue;
    }
    if (arg === '--counterexample') {
      options.counterexamples.push(readRequiredValue(argv, index, '--counterexample'));
      index += 1;
      continue;
    }
    if (arg === '--evidence-manifest') {
      options.evidenceManifests.push(readRequiredValue(argv, index, '--evidence-manifest'));
      index += 1;
      continue;
    }
    if (arg === '--producer-summary') {
      options.producerSummaries.push(readRequiredValue(argv, index, '--producer-summary'));
      index += 1;
      continue;
    }
    if (arg === '--boundary-map-summary') {
      options.boundaryMapSummaries.push(readRequiredValue(argv, index, '--boundary-map-summary'));
      index += 1;
      continue;
    }
    if (arg === '--claim-evidence-manifest') {
      options.claimEvidenceManifests.push(readRequiredValue(argv, index, '--claim-evidence-manifest'));
      index += 1;
      continue;
    }
    if (arg === '--policy-decision') {
      options.policyDecision = readRequiredValue(argv, index, '--policy-decision');
      index += 1;
      continue;
    }
    if (arg === '--security-claims') {
      options.securityClaims = readRequiredValue(argv, index, '--security-claims');
      index += 1;
      continue;
    }
    if (arg === '--security-findings') {
      options.securityFindings = readRequiredValue(argv, index, '--security-findings');
      index += 1;
      continue;
    }
    if (arg === '--security-review') {
      options.securityReview = readRequiredValue(argv, index, '--security-review');
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = readRequiredValue(argv, index, '--output-json');
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = readRequiredValue(argv, index, '--output-md');
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.assuranceProfile) {
    throw new Error('--assurance-profile is required');
  }
  return options;
};

const ensureFile = (targetPath, label) => {
  const resolved = path.resolve(targetPath);
  if (!fs.existsSync(resolved) || !fs.statSync(resolved).isFile()) {
    throw new Error(`${label} does not exist: ${resolved}`);
  }
  return resolved;
};

const readJson = (targetPath) => JSON.parse(fs.readFileSync(targetPath, 'utf8'));

const readStructured = (targetPath, label) => {
  const raw = fs.readFileSync(targetPath, 'utf8');
  const lowerPath = targetPath.toLowerCase();
  if (lowerPath.endsWith('.yaml') || lowerPath.endsWith('.yml')) {
    const parsed = yaml.parse(raw);
    return ensureObject(parsed, label);
  }
  return ensureObject(JSON.parse(raw), label);
};

const ensureObject = (value, label) => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    throw new Error(`${label} must be an object`);
  }
  return value;
};

const ensureArray = (value, label) => {
  if (!Array.isArray(value)) {
    throw new Error(`${label} must be an array`);
  }
  return value;
};

const maybeString = (value) => (value === null || value === undefined ? '' : String(value).trim());

const uniqueSorted = (values) => Array.from(new Set(values.filter(Boolean))).sort();

const normalizeSecurityClaimType = (value) => {
  const candidate = maybeString(value).toLowerCase();
  return SECURITY_CLAIM_TYPES.has(candidate) ? candidate : null;
};

const normalizeAssumptionHandling = (handling, effectiveResult, findingId) => {
  const mode = ASSUMPTION_HANDLING_MODES.has(maybeString(handling?.mode))
    ? maybeString(handling.mode)
    : (effectiveResult === 'candidate' || effectiveResult === 'needs-human-review' || effectiveResult === 'confirmed'
        ? 'assumption-validation-required'
        : 'residual-risk');
  const rationale = maybeString(handling?.rationale)
    || (mode === 'assumption-validation-required'
      ? `Assumption-derived finding ${findingId} requires environment, scope, and trust-boundary validation.`
      : `Assumption-derived finding ${findingId} is tracked as residual-risk evidence.`);
  return {
    mode,
    findingId,
    reviewResult: effectiveResult || 'unknown',
    rationale,
    evidenceRefs: uniqueSorted(Array.isArray(handling?.evidenceRefs) ? handling.evidenceRefs.map((entry) => maybeString(entry)) : []),
  };
};

const sortLanes = (values) =>
  Array.from(new Set(values.filter(Boolean))).sort((left, right) => {
    const leftIndex = LANE_ORDER.indexOf(left);
    const rightIndex = LANE_ORDER.indexOf(right);
    if (leftIndex >= 0 && rightIndex >= 0) {
      return leftIndex - rightIndex;
    }
    if (leftIndex >= 0) return -1;
    if (rightIndex >= 0) return 1;
    return left.localeCompare(right);
  });

export function isExecutedAsMain(metaUrl, argvPath = process.argv[1]) {
  if (!argvPath) return false;
  return metaUrl === `file://${path.resolve(argvPath)}`;
}

const pushWarning = (warnings, code, message, extra = {}) => {
  if (!WARNING_CODES.has(code)) {
    throw new Error(`Unknown warning code: ${code}`);
  }
  warnings.push({
    code,
    message,
    claimId: extra.claimId ?? null,
    artifactPath: extra.artifactPath ?? null,
  });
};

const writeFile = (targetPath, content) => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  fs.writeFileSync(targetPath, content, 'utf8');
};

const markdownCell = (value) =>
  String(value ?? '')
    .replace(/\\/g, '\\\\')
    .replace(/\|/g, '\\|')
    .replace(/\r?\n/g, '<br>');

const renderTable = (headers, rows) => {
  const header = `| ${headers.map(markdownCell).join(' | ')} |`;
  const separator = `| ${headers.map(() => '---').join(' | ')} |`;
  const body = rows.map((row) => `| ${row.map(markdownCell).join(' | ')} |`);
  return [header, separator, ...body].join('\n');
};

const countBy = (values, knownKeys) => {
  const counts = Object.fromEntries(knownKeys.map((key) => [key, 0]));
  for (const value of values) {
    const key = knownKeys.includes(value) ? value : 'other';
    counts[key] = (counts[key] ?? 0) + 1;
  }
  return counts;
};

const readOptionalJsonInputs = (targetPaths, label) =>
  targetPaths.map((targetPath) => {
    const resolvedPath = ensureFile(targetPath, label);
    return { path: resolvedPath, payload: readJson(resolvedPath) };
  });

const shortRefValue = (value) => {
  if (value && typeof value === 'object') {
    const kind = maybeString(value.kind);
    const refId = maybeString(value.refId);
    if (kind || refId) return `${kind}:${refId}`;
    const id = maybeString(value.id);
    if (id) return id;
  }
  return maybeString(value);
};

const summarizeProducerSignals = (producerSummaryInputs) => {
  const artifactPaths = producerSummaryInputs.map((entry) => entry.path).sort();
  const producers = producerSummaryInputs
    .map(({ payload }) => ({
      id: maybeString(payload.producer?.id) || 'unknown',
      displayName: maybeString(payload.producer?.displayName) || maybeString(payload.producer?.id) || 'unknown',
      category: maybeString(payload.producer?.category) || 'unknown',
    }))
    .sort((left, right) => left.id.localeCompare(right.id));
  const reportOnlyFindings = producerSummaryInputs.reduce(
    (total, { payload }) =>
      total
      + Number(payload.summary?.reportOnlyFindings ?? payload.controlPlaneRouting?.reportOnlyFindings?.length ?? 0),
    0,
  );
  const missingEvidence = producerSummaryInputs.reduce(
    (total, { payload }) =>
      total + Number(payload.summary?.missingEvidence ?? payload.controlPlaneRouting?.missingEvidence?.length ?? 0),
    0,
  );
  const producerAssertions = producerSummaryInputs.reduce(
    (total, { payload }) =>
      total
      + Number(payload.summary?.rawSignals ?? payload.producerAssertions?.rawSignals?.length ?? 0)
      + Number(payload.summary?.claimsMentioned ?? payload.producerAssertions?.claimsMentioned?.length ?? 0),
    0,
  );
  const findingRefs = producerSummaryInputs
    .flatMap(({ payload }) => (Array.isArray(payload.controlPlaneRouting?.reportOnlyFindings)
      ? payload.controlPlaneRouting.reportOnlyFindings
      : []))
    .map((finding) => ({
      id: maybeString(finding.id) || 'unknown',
      kind: maybeString(finding.kind) || 'unknown',
      summary: maybeString(finding.summary) || 'No summary provided.',
    }))
    .slice(0, 25);
  const emittedJudgments = producerSummaryInputs.filter(({ payload }) => payload.controlPlaneJudgment?.emitsDecision);

  return {
    status: artifactPaths.length === 0
      ? 'not-provided'
      : reportOnlyFindings > 0 || missingEvidence > 0
        ? 'report-only-findings'
        : 'present',
    artifactPaths,
    producers,
    producerAssertions,
    missingEvidence,
    reportOnlyFindings,
    findingRefs,
    controlPlaneJudgment: {
      emittedDecisionCount: emittedJudgments.length,
      expected: 'producer-output-is-not-control-plane-judgment',
    },
  };
};

const summarizeContextPackSurface = (contextPackPaths) => ({
  status: contextPackPaths.length > 0 ? 'present' : 'not-provided',
  artifactPaths: uniqueSorted(contextPackPaths.map((targetPath) => path.resolve(targetPath))),
  preflightStatus: 'not-recorded-in-artifact',
  note: 'Context Pack conflict is a PR/reviewer control-plane record; this summary only lists Context Pack inputs.',
});

const boundaryStatusRank = {
  'not-provided': 0,
  ok: 1,
  skipped: 2,
  unresolved: 3,
  drift: 4,
};

const summarizeBoundaryMapSurface = (boundaryMapSummaryInputs) => {
  const artifactPaths = boundaryMapSummaryInputs.map((entry) => entry.path).sort();
  const statuses = boundaryMapSummaryInputs.map(({ payload }) => maybeString(payload.status) || 'unresolved');
  const status = statuses.reduce(
    (current, candidate) =>
      (boundaryStatusRank[candidate] ?? boundaryStatusRank.unresolved) > (boundaryStatusRank[current] ?? 0)
        ? candidate
        : current,
    artifactPaths.length > 0 ? 'ok' : 'not-provided',
  );
  const totalFindings = boundaryMapSummaryInputs.reduce(
    (total, { payload }) => total + Number(payload.counts?.totalFindings ?? 0),
    0,
  );
  const reviewEvidence = boundaryMapSummaryInputs
    .flatMap(({ payload }) => (Array.isArray(payload.reviewEvidence) ? payload.reviewEvidence : []))
    .map((entry) => ({
      type: maybeString(entry.type) || 'unknown',
      severity: maybeString(entry.severity) || 'info',
      file: maybeString(entry.file) || 'unknown',
      slice: maybeString(entry.slice) || null,
      ref: shortRefValue(entry.ref) || null,
      expectedOwner: maybeString(entry.expectedOwner) || 'n/a',
      observedDependency: maybeString(entry.observedDependency) || 'n/a',
      message: maybeString(entry.message) || 'No message provided.',
    }))
    .slice(0, 50);

  return {
    status,
    artifactPaths,
    reviewStatuses: uniqueSorted(
      boundaryMapSummaryInputs.map(({ payload }) => maybeString(payload.reviewStatus)).filter(Boolean),
    ),
    evidenceKind: artifactPaths.length > 0 ? 'design-boundary' : null,
    totalFindings,
    reviewEvidence,
    interpretation: artifactPaths.length > 0
      ? 'Boundary Map drift is a design-boundary evidence gap; it is not proof evidence and not a proof failure by itself.'
      : 'No boundary-map summary was provided.',
  };
};

const normalizeManifestStatus = (value) => {
  const status = maybeString(value).toLowerCase();
  if (['satisfied', 'partial', 'waived', 'unresolved', 'failed'].includes(status)) {
    return status;
  }
  return 'other';
};

const evidenceRefsContainRuntime = (claim) =>
  (Array.isArray(claim.evidenceRefs) ? claim.evidenceRefs : []).some((entry) => maybeString(entry.kind) === 'runtime');

const summarizeClaimEvidenceSurface = (claimEvidenceManifestInputs, claimSummaries) => {
  const artifactPaths = claimEvidenceManifestInputs.map((entry) => entry.path).sort();
  const manifestClaims = claimEvidenceManifestInputs.flatMap(({ payload }) =>
    Array.isArray(payload.claims) ? payload.claims : [],
  );
  const manifestStatusCounts = countBy(
    manifestClaims.map((claim) => normalizeManifestStatus(claim.status)),
    ['satisfied', 'partial', 'waived', 'unresolved', 'failed', 'other'],
  );
  const assuranceStatusCounts = countBy(
    claimSummaries.map((claim) => maybeString(claim.status) || 'other'),
    ['satisfied', 'warning', 'other'],
  );
  const missingEvidenceClaims = manifestClaims
    .filter((claim) => Array.isArray(claim.missingEvidenceRefs) && claim.missingEvidenceRefs.length > 0)
    .map((claim) => ({
      claimId: maybeString(claim.id) || 'unknown',
      status: normalizeManifestStatus(claim.status),
      missingEvidenceRefs: claim.missingEvidenceRefs.map((entry) => shortRefValue(entry)).filter(Boolean),
    }))
    .sort((left, right) => left.claimId.localeCompare(right.claimId));
  const unresolvedClaims = manifestClaims
    .filter((claim) => ['partial', 'unresolved', 'failed'].includes(normalizeManifestStatus(claim.status)))
    .map((claim) => ({
      claimId: maybeString(claim.id) || 'unknown',
      status: normalizeManifestStatus(claim.status),
      reason: Array.isArray(claim.missingEvidenceRefs) && claim.missingEvidenceRefs.length > 0
        ? 'missing-evidence'
        : 'status-not-satisfied',
    }))
    .sort((left, right) => left.claimId.localeCompare(right.claimId));
  const runtimeMitigatedClaims = manifestClaims
    .filter((claim) => evidenceRefsContainRuntime(claim))
    .map((claim) => ({
      claimId: maybeString(claim.id) || 'unknown',
      status: normalizeManifestStatus(claim.status),
      interpretation: 'runtime-mitigated is operational mitigation, not proof',
    }))
    .sort((left, right) => left.claimId.localeCompare(right.claimId));

  return {
    status: artifactPaths.length > 0 ? 'present' : 'not-provided',
    artifactPaths,
    manifestStatusCounts,
    assuranceStatusCounts,
    missingEvidenceClaims,
    unresolvedClaims,
    runtimeMitigatedClaims,
  };
};

const summarizeWaiverSurface = (claimEvidenceManifestInputs, policyDecisionInput) => {
  const manifestClaims = claimEvidenceManifestInputs.flatMap(({ payload }) =>
    Array.isArray(payload.claims) ? payload.claims : [],
  );
  const manifestWaivers = manifestClaims.flatMap((claim) =>
    (Array.isArray(claim.waiverRefs) ? claim.waiverRefs : []).map((waiver) => ({
      id: shortRefValue(waiver) || 'unknown',
      claimId: maybeString(claim.id) || 'unknown',
      status: maybeString(waiver.status) || 'unknown',
      owner: maybeString(waiver.owner) || null,
      expires: maybeString(waiver.expires) || null,
      reason: maybeString(waiver.reason) || null,
      source: 'claim-evidence-manifest',
    })),
  );
  const policyAssurance = policyDecisionInput?.payload?.evaluation?.assurance;
  const policyWaivers = Array.isArray(policyAssurance?.waivers)
    ? policyAssurance.waivers.map((waiver) => ({
        id: maybeString(waiver.id) || 'unknown',
        claimId: maybeString(waiver.claimId) || 'unknown',
        status: maybeString(waiver.status) || 'unknown',
        owner: maybeString(waiver.owner) || null,
        expires: maybeString(waiver.expires) || null,
        reason: maybeString(waiver.reason) || null,
        source: 'policy-decision',
      }))
    : [];
  const waiverStatusRank = {
    unknown: 0,
    active: 1,
    expiringSoon: 2,
    expired: 3,
    orphan: 4,
  };
  const selectWaiverStatus = (left, right) =>
    (waiverStatusRank[right] ?? waiverStatusRank.unknown) > (waiverStatusRank[left] ?? waiverStatusRank.unknown)
      ? right
      : left;
  const waiverRefsByKey = new Map();
  for (const waiver of [...manifestWaivers, ...policyWaivers]) {
    const key = `${waiver.claimId}:${waiver.id}`;
    const existing = waiverRefsByKey.get(key);
    waiverRefsByKey.set(key, existing
      ? {
          ...existing,
          status: selectWaiverStatus(existing.status, waiver.status),
          owner: existing.owner ?? waiver.owner,
          expires: existing.expires ?? waiver.expires,
          reason: existing.reason ?? waiver.reason,
          source: uniqueSorted([...existing.source.split(', '), waiver.source]).join(', '),
        }
      : waiver);
  }
  const waiverRefs = Array.from(waiverRefsByKey.values())
    .sort((left, right) => `${left.claimId}:${left.id}:${left.source}`.localeCompare(`${right.claimId}:${right.id}:${right.source}`));

  return {
    active: Number(
      policyAssurance?.summary?.activeWaivers
        ?? waiverRefs.filter((waiver) => waiver.status === 'active' || waiver.status === 'expiringSoon').length,
    ),
    expiringSoon: Number(policyAssurance?.summary?.expiringSoonWaivers ?? 0),
    expired: Number(policyAssurance?.summary?.expiredWaivers ?? 0),
    orphan: Number(policyAssurance?.summary?.orphanWaivers ?? 0),
    claims: uniqueSorted(waiverRefs.map((waiver) => waiver.claimId)),
    waiverRefs,
    interpretation: 'Waived claims require explicit review; waived is not satisfied.',
  };
};

const summarizePolicyDecisionSurface = (policyDecisionInput) => {
  if (!policyDecisionInput) {
    return {
      status: 'not-provided',
      artifactPath: null,
      mode: null,
      result: null,
      ok: null,
      enforced: false,
      summary: null,
    };
  }
  const assurance = policyDecisionInput.payload?.evaluation?.assurance;
  const mode = maybeString(assurance?.mode) || null;
  const result = maybeString(assurance?.result) || null;
  return {
    status: 'present',
    artifactPath: policyDecisionInput.path,
    mode,
    result,
    ok: typeof policyDecisionInput.payload?.evaluation?.ok === 'boolean'
      ? policyDecisionInput.payload.evaluation.ok
      : null,
    enforced: mode !== null && mode !== 'report-only',
    summary: assurance?.summary && typeof assurance.summary === 'object'
      ? {
          totalClaims: Number(assurance.summary.totalClaims ?? 0),
          pass: Number(assurance.summary.pass ?? 0),
          waived: Number(assurance.summary.waived ?? 0),
          reportOnly: Number(assurance.summary.reportOnly ?? 0),
          block: Number(assurance.summary.block ?? 0),
          activeWaivers: Number(assurance.summary.activeWaivers ?? 0),
        }
      : null,
  };
};

const buildResidualRisks = ({ assuranceClaims, producerSignals, boundaryMap, claimEvidence, waivers, policyDecision }) => {
  const residualRisks = [];
  for (const claim of assuranceClaims.filter((entry) => entry.status === 'warning')) {
    residualRisks.push({
      kind: 'assurance-warning-claim',
      claimId: claim.claimId,
      severity: (claim.criticality === 'high' || claim.criticality === 'critical') ? 'high' : 'review',
      reason: `Assurance summary status is warning; missingLanes=${claim.missingLanes.join(', ') || 'none'}, missingEvidenceKinds=${claim.missingEvidenceKinds.join(', ') || 'none'}, warnings=${claim.independenceWarnings.join(', ') || 'none'}.`,
      source: 'assurance-summary',
    });
  }
  if (producerSignals.reportOnlyFindings > 0 || producerSignals.missingEvidence > 0) {
    residualRisks.push({
      kind: 'producer-report-only-finding',
      claimId: null,
      severity: 'review',
      reason: `Producer summary reports ${producerSignals.reportOnlyFindings} report-only finding(s) and ${producerSignals.missingEvidence} missing evidence item(s).`,
      source: 'producer-summary',
    });
  }
  if (boundaryMap.status === 'drift' || boundaryMap.status === 'unresolved') {
    residualRisks.push({
      kind: 'boundary-map-evidence-gap',
      claimId: null,
      severity: 'review',
      reason: `Boundary Map summary status is ${boundaryMap.status}; inspect design-boundary evidence before treating affected claims as supported.`,
      source: 'boundary-map-summary',
    });
  }
  for (const claim of claimEvidence.missingEvidenceClaims) {
    residualRisks.push({
      kind: 'missing-evidence',
      claimId: claim.claimId,
      severity: 'review',
      reason: `${claim.status} claim has missing evidence refs: ${claim.missingEvidenceRefs.join(', ') || 'n/a'}.`,
      source: 'claim-evidence-manifest',
    });
  }
  for (const claim of claimEvidence.unresolvedClaims) {
    residualRisks.push({
      kind: 'unresolved-claim',
      claimId: claim.claimId,
      severity: 'review',
      reason: `Claim status is ${claim.status}; do not treat it as satisfied.`,
      source: 'claim-evidence-manifest',
    });
  }
  if (waivers.active > 0 || waivers.expiringSoon > 0 || waivers.expired > 0 || waivers.orphan > 0) {
    residualRisks.push({
      kind: 'waiver-review-required',
      claimId: null,
      severity: waivers.expired > 0 || waivers.orphan > 0 ? 'high' : 'review',
      reason: `Waiver summary: active=${waivers.active}, expiringSoon=${waivers.expiringSoon}, expired=${waivers.expired}, orphan=${waivers.orphan}.`,
      source: 'claim-evidence-manifest/policy-decision',
    });
  }
  if (policyDecision.summary?.block > 0 || policyDecision.result === 'block') {
    residualRisks.push({
      kind: 'policy-block',
      claimId: null,
      severity: 'high',
      reason: `Policy decision assurance result is ${policyDecision.result ?? 'unknown'} with block=${policyDecision.summary?.block ?? 0}.`,
      source: 'policy-decision',
    });
  }
  return residualRisks.sort((left, right) => `${left.severity}:${left.kind}:${left.claimId ?? ''}`.localeCompare(`${right.severity}:${right.kind}:${right.claimId ?? ''}`));
};

const chooseRecommendedReviewerAction = ({ assuranceClaims, producerSignals, boundaryMap, claimEvidence, waivers, policyDecision, residualRisks }) => {
  if (policyDecision.summary?.block > 0 || policyDecision.result === 'block') {
    return {
      action: 'review-policy-block',
      reason: 'Policy decision reports a blocking assurance result; inspect policy-decision before any release judgment.',
    };
  }
  if (boundaryMap.status === 'drift' || boundaryMap.status === 'unresolved') {
    return {
      action: 'review-boundary-map',
      reason: `Boundary Map status is ${boundaryMap.status}; treat it as a design-boundary evidence gap, not a proof failure.`,
    };
  }
  const assuranceWarningClaims = assuranceClaims.filter((entry) => entry.status === 'warning').length;
  if (claimEvidence.unresolvedClaims.length > 0 || claimEvidence.missingEvidenceClaims.length > 0 || assuranceWarningClaims > 0) {
    return {
      action: 'review-unresolved-claims',
      reason: `Assurance warning claims=${assuranceWarningClaims}, unresolved/partial manifest claims=${claimEvidence.unresolvedClaims.length}, claims with missing evidence=${claimEvidence.missingEvidenceClaims.length}.`,
    };
  }
  if (waivers.active > 0 || waivers.expiringSoon > 0 || waivers.expired > 0 || waivers.orphan > 0) {
    return {
      action: 'review-waivers',
      reason: `Waivers require human review: active=${waivers.active}, expiringSoon=${waivers.expiringSoon}, expired=${waivers.expired}, orphan=${waivers.orphan}.`,
    };
  }
  if (producerSignals.reportOnlyFindings > 0 || producerSignals.missingEvidence > 0) {
    return {
      action: 'review-producer-findings',
      reason: `Producer output has report-only findings=${producerSignals.reportOnlyFindings}; these are not control-plane judgments.`,
    };
  }
  if (residualRisks.length > 0) {
    return {
      action: 'review-residual-risks',
      reason: `${residualRisks.length} residual risk item(s) remain in the review surface.`,
    };
  }
  return {
    action: 'ready-for-human-judgment',
    reason: 'No unresolved, waived, missing-evidence, producer report-only, or boundary-map findings were surfaced; this is still not an automatic merge approval.',
  };
};

const buildReviewSurface = ({ summary, options, producerSummaryInputs, boundaryMapSummaryInputs, claimEvidenceManifestInputs, policyDecisionInput }) => {
  const producerSignals = summarizeProducerSignals(producerSummaryInputs);
  const contextPack = summarizeContextPackSurface(options.contextPacks);
  const boundaryMap = summarizeBoundaryMapSurface(boundaryMapSummaryInputs);
  const claimEvidence = summarizeClaimEvidenceSurface(claimEvidenceManifestInputs, summary.claims);
  const waivers = summarizeWaiverSurface(claimEvidenceManifestInputs, policyDecisionInput);
  const policyDecision = summarizePolicyDecisionSurface(policyDecisionInput);
  const residualRisks = buildResidualRisks({
    assuranceClaims: summary.claims,
    producerSignals,
    boundaryMap,
    claimEvidence,
    waivers,
    policyDecision,
  });
  const recommendedReviewerAction = chooseRecommendedReviewerAction({
    assuranceClaims: summary.claims,
    producerSignals,
    boundaryMap,
    claimEvidence,
    waivers,
    policyDecision,
    residualRisks,
  });

  return {
    schemaVersion: 'assurance-review-surface/v1',
    summary: {
      recommendedReviewerAction: recommendedReviewerAction.action,
      assuranceClaimStatusCounts: claimEvidence.assuranceStatusCounts,
      manifestClaimStatusCounts: claimEvidence.manifestStatusCounts,
      unresolvedClaims: claimEvidence.unresolvedClaims.length,
      waivedClaims: claimEvidence.manifestStatusCounts.waived,
      missingEvidenceClaims: claimEvidence.missingEvidenceClaims.length,
      activeWaivers: waivers.active,
      producerReportOnlyFindings: producerSignals.reportOnlyFindings,
      boundaryMapStatus: boundaryMap.status,
      policyDecisionResult: policyDecision.result,
    },
    producerSignals,
    contextPack,
    boundaryMap,
    claimEvidence,
    waivers,
    policyDecision,
    residualRisks,
    recommendedReviewerAction,
    interpretationNotes: [
      'Producer assertions remain producer assertions; control-plane judgment must come from reviewed, schema-backed evidence and policy artifacts.',
      'tested and proved are distinct evidence outcomes; runtime-mitigated is not proof.',
      'waived is an explicit exception state and must not be counted as satisfied.',
      'This review surface helps reviewers identify support and gaps; it is not an automatic merge approval.',
    ],
  };
};

const defaultMinIndependentSources = (claim) => {
  if (Number.isInteger(claim.minIndependentSources) && claim.minIndependentSources > 0) {
    return claim.minIndependentSources;
  }
  return claim.criticality === 'high' || claim.criticality === 'critical' ? 2 : 1;
};

const evidenceKindFromCounterexampleBackend = (backend) => {
  switch (backend) {
    case 'property':
    case 'pbt':
      return 'property';
    case 'unit':
      return 'unit';
    case 'integration':
    case 'mbt':
      return 'integration';
    case 'mutation':
      return 'mutation';
    case 'fuzz':
      return 'fuzz';
    case 'differential':
      return 'differential';
    case 'runtime':
    case 'monitor':
      return 'runtime-monitor';
    case 'alert':
      return 'runtime-alert';
    case 'rollout':
      return 'runtime-rollout-guard';
    case 'conformance':
      return 'conformance';
    case 'lean':
    case 'kani':
      return 'proof';
    default:
      return 'model-check';
  }
};

const laneFromCounterexampleBackend = (backend) => {
  switch (backend) {
    case 'property':
    case 'pbt':
    case 'unit':
    case 'integration':
    case 'mbt':
      return 'behavior';
    case 'mutation':
    case 'fuzz':
    case 'differential':
      return 'adversarial';
    case 'lean':
    case 'kani':
      return 'proof';
    case 'runtime':
    case 'monitor':
    case 'alert':
    case 'rollout':
      return 'runtime';
    case 'conformance':
    case 'tlc':
    case 'apalache':
    case 'alloy':
    case 'smt':
    case 'csp':
    case 'spin':
    case 'model':
    default:
      return 'model';
  }
};

const sourceKindFromLane = (lane) => {
  if (lane === 'spec') return 'spec-derived';
  if (lane === 'model' || lane === 'proof') return 'model-derived';
  if (lane === 'runtime') return 'runtime-derived';
  if (lane === 'behavior' || lane === 'adversarial') return 'source-derived';
  return 'unknown';
};

const formalLaneMapping = (name) => {
  switch (name) {
    case 'conformance':
    case 'tla':
    case 'apalache':
    case 'alloy':
    case 'smt':
    case 'csp':
    case 'spin':
    case 'model':
      return { lane: 'model', kind: name === 'conformance' ? 'conformance' : 'model-check' };
    case 'lean':
    case 'kani':
      return { lane: 'proof', kind: 'proof' };
    default:
      return null;
  }
};

const normalizeEvidenceEntry = (entry, defaults = {}) => {
  const normalized = {
    lane: maybeString(entry.lane),
    kind: maybeString(entry.kind),
    sourceKind: maybeString(entry.sourceKind || defaults.sourceKind),
    origin: maybeString(entry.origin || defaults.origin),
    status: maybeString(entry.status || 'observed'),
    artifactPath: maybeString(entry.artifactPath || defaults.artifactPath) || null,
    detail: maybeString(entry.detail || defaults.detail) || null,
    claimRefs: uniqueSorted(
      Array.isArray(entry.claimRefs)
        ? entry.claimRefs.map((value) => maybeString(value))
        : Array.isArray(entry.claimIds)
          ? entry.claimIds.map((value) => maybeString(value))
          : [],
    ),
    generatorLineage: maybeString(entry.generatorLineage || defaults.generatorLineage) || null,
  };

  if (!LANE_ORDER.includes(normalized.lane)) {
    throw new Error(`Unsupported lane: ${normalized.lane}`);
  }
  if (!normalized.kind) {
    throw new Error('Evidence kind is required');
  }
  if (!SOURCE_KINDS.has(normalized.sourceKind)) {
    throw new Error(`Unsupported sourceKind: ${normalized.sourceKind}`);
  }
  if (!normalized.origin) {
    throw new Error('Evidence origin is required');
  }
  if (normalized.status !== 'observed' && normalized.status !== 'warning') {
    throw new Error(`Unsupported evidence status: ${normalized.status}`);
  }
  return normalized;
};

const buildClaimState = (claim) => ({
  claimId: claim.id,
  statement: claim.statement,
  criticality: claim.criticality,
  targetLevel: claim.targetLevel,
  securityClaimType: normalizeSecurityClaimType(claim.securityClaimType ?? claim.type),
  assumptionHandling: [],
  minIndependentSources: defaultMinIndependentSources(claim),
  requiredLanes: uniqueSorted(claim.requiredLanes ?? []),
  requiredEvidenceKinds: uniqueSorted(claim.requiredEvidenceKinds ?? []),
  evidence: [],
  counterexamples: {
    open: 0,
    resolved: 0,
    acceptedRisk: 0,
    total: 0,
  },
});

const addEvidenceForClaims = (claimStateMap, claimIds, evidence, warnings, artifactPath) => {
  for (const claimId of claimIds) {
    const claimState = claimStateMap.get(claimId);
    if (!claimState) {
      pushWarning(
        warnings,
        'unrecognized-evidence-claim',
        `Evidence references unknown claim "${claimId}".`,
        { claimId, artifactPath },
      );
      continue;
    }
    claimState.evidence.push({
      ...evidence,
      claimRefs: uniqueSorted([...(evidence.claimRefs ?? []), claimId]),
    });
  }
};

const collectContextPackReferences = (contextPackPaths, profileId, claimStateMap, warnings) => {
  const claimRefsById = new Map();

  for (const contextPackPath of contextPackPaths) {
    const resolvedPath = ensureFile(contextPackPath, 'Context Pack');
    const contextPack = readStructured(resolvedPath, `Context Pack (${resolvedPath})`);
    const assurance = ensureObject(contextPack.assurance ?? {}, `Context Pack assurance (${resolvedPath})`);
    if (!assurance.profile || !Array.isArray(assurance.claim_refs)) {
      continue;
    }
    if (assurance.profile !== profileId) {
      pushWarning(
        warnings,
        'context-pack-profile-mismatch',
        `Context Pack assurance profile "${assurance.profile}" does not match "${profileId}".`,
        { artifactPath: resolvedPath },
      );
      continue;
    }

    for (const rawClaimId of assurance.claim_refs) {
      const claimId = maybeString(rawClaimId);
      if (!claimId) continue;
      if (!claimStateMap.has(claimId)) {
        pushWarning(
          warnings,
          'unknown-claim-ref',
          `Context Pack references unknown claim "${claimId}".`,
          { claimId, artifactPath: resolvedPath },
        );
        continue;
      }
      const current = claimRefsById.get(claimId) ?? [];
      current.push(resolvedPath);
      claimRefsById.set(claimId, current);
      claimStateMap.get(claimId).evidence.push(
        normalizeEvidenceEntry(
          {
            lane: 'spec',
            kind: 'schema',
            sourceKind: 'spec-derived',
            origin: 'context-pack',
            status: 'observed',
            artifactPath: resolvedPath,
            detail: 'Context Pack assurance reference',
            claimRefs: [claimId],
            generatorLineage: 'context-pack-v1',
          },
        ),
      );
    }
  }

  return claimRefsById;
};

const claimIdsForGlobalEvidence = (claimStateMap, contextPackRefs) => {
  const scopedClaimIds = uniqueSorted(Array.from(contextPackRefs.keys()));
  return scopedClaimIds.length > 0 ? scopedClaimIds : Array.from(claimStateMap.keys());
};

const ingestVerifyLiteSummary = (summaryPath, claimStateMap, contextPackRefs, warnings) => {
  if (!summaryPath) return;
  const resolvedPath = ensureFile(summaryPath, 'Verify Lite summary');
  const summary = readJson(resolvedPath);
  const artifacts = ensureObject(summary.artifacts ?? {}, 'verify-lite artifacts');
  const targetClaims = claimIdsForGlobalEvidence(claimStateMap, contextPackRefs);

  const evidenceEntries = [
    ['contextPackReportJson', 'spec', 'schema', 'spec-derived', 'verify-lite/context-pack'],
    ['contextPackFunctorReportJson', 'spec', 'schema', 'spec-derived', 'verify-lite/context-pack'],
    ['contextPackNaturalTransformationReportJson', 'spec', 'natural-transformation', 'spec-derived', 'verify-lite/context-pack'],
    ['contextPackProductCoproductReportJson', 'spec', 'product-coproduct', 'spec-derived', 'verify-lite/context-pack'],
    ['contextPackPhase5ReportJson', 'spec', 'schema', 'spec-derived', 'verify-lite/context-pack'],
    ['mutationSummary', 'adversarial', 'mutation', 'source-derived', 'verify-lite/mutation'],
    ['conformanceSummary', 'model', 'conformance', 'model-derived', 'verify-lite/conformance'],
  ];

  for (const [key, lane, kind, sourceKind, generatorLineage] of evidenceEntries) {
    const artifactPath = maybeString(artifacts[key]);
    if (!artifactPath) continue;
    const evidence = normalizeEvidenceEntry({
      lane,
      kind,
      sourceKind,
      origin: 'verify-lite',
      artifactPath,
      detail: `verify-lite referenced ${key}`,
      generatorLineage,
    });
    addEvidenceForClaims(claimStateMap, targetClaims, evidence, warnings, artifactPath);
  }
};

const ingestFormalSummary = (summaryPath, claimStateMap, contextPackRefs, warnings) => {
  const resolvedPath = ensureFile(summaryPath, 'Formal summary');
  const summary = readJson(resolvedPath);
  const targetClaims = claimIdsForGlobalEvidence(claimStateMap, contextPackRefs);
  const tool = maybeString(summary.tool);
  const results = Array.isArray(summary.results) ? summary.results : [];
  const candidates = results.length > 0 ? results : [{ name: tool, status: summary.status }];

  for (const result of candidates) {
    const name = maybeString(result.name || tool);
    const status = maybeString(result.status || summary.status);
    const mapping = formalLaneMapping(name);
    if (!mapping || status !== 'ok') continue;
    const evidence = normalizeEvidenceEntry({
      lane: mapping.lane,
      kind: mapping.kind,
      sourceKind: 'model-derived',
      origin: 'formal-summary',
      artifactPath: resolvedPath,
      detail: `formal summary result "${name}" is ok`,
      generatorLineage: `formal-summary/${tool || name}`,
    });
    addEvidenceForClaims(claimStateMap, targetClaims, evidence, warnings, resolvedPath);
  }
};

const ingestConformanceReport = (summaryPath, claimStateMap, contextPackRefs, warnings) => {
  if (!summaryPath) return;
  const resolvedPath = ensureFile(summaryPath, 'Conformance report');
  const summary = readJson(resolvedPath);
  const targetClaims = claimIdsForGlobalEvidence(claimStateMap, contextPackRefs);
  const runsAnalyzed = Number(summary.runsAnalyzed ?? 0);
  const status = maybeString(summary.status).toLowerCase();
  if (!Number.isFinite(runsAnalyzed) || runsAnalyzed <= 0 || status !== 'success') return;
  const evidence = normalizeEvidenceEntry({
    lane: 'model',
    kind: 'conformance',
    sourceKind: 'model-derived',
    origin: 'conformance-report',
    artifactPath: resolvedPath,
    detail: `conformance report analyzed ${runsAnalyzed} run(s)`,
    generatorLineage: 'conformance-report',
  });
  addEvidenceForClaims(claimStateMap, targetClaims, evidence, warnings, resolvedPath);
};

const ingestCounterexample = (counterexamplePath, claimStateMap, warnings, summaryState) => {
  const resolvedPath = ensureFile(counterexamplePath, 'Counterexample');
  const counterexample = readJson(resolvedPath);
  const rawClaimIds = Array.isArray(counterexample.claimIds) ? counterexample.claimIds : [];
  const claimIds = uniqueSorted(rawClaimIds.map((value) => maybeString(value)));
  const backend = maybeString(counterexample.backend).toLowerCase() || 'unknown';
  const lane = laneFromCounterexampleBackend(backend);
  const sourceKind = sourceKindFromLane(lane);
  const baseKind = evidenceKindFromCounterexampleBackend(backend);
  const triageStatus = maybeString(counterexample.triageStatus).toLowerCase() || 'open';
  const morphismIds = Array.isArray(counterexample.morphismIds)
    ? uniqueSorted(counterexample.morphismIds.map((value) => maybeString(value)))
    : [];
  const detailParts = [];
  if (counterexample.violated?.name) detailParts.push(`violated=${counterexample.violated.name}`);
  if (morphismIds.length > 0) detailParts.push(`morphisms=${morphismIds.join(',')}`);
  if (triageStatus) detailParts.push(`triage=${triageStatus}`);
  const detail = detailParts.join('; ');

  if (claimIds.length === 0) {
    summaryState.unlinkedCounterexamples += 1;
    pushWarning(
      warnings,
      'unlinked-counterexample',
      'Counterexample is not linked to any claim.',
      { artifactPath: resolvedPath },
    );
    return;
  }

  const primaryEvidence = normalizeEvidenceEntry({
    lane,
    kind: baseKind,
    sourceKind,
    origin: 'counterexample',
    artifactPath: resolvedPath,
    detail,
    claimRefs: claimIds,
    generatorLineage: backend || 'counterexample',
  });
  addEvidenceForClaims(claimStateMap, claimIds, primaryEvidence, warnings, resolvedPath);

  const closureEvidence =
    triageStatus === 'resolved'
      ? normalizeEvidenceEntry({
          lane,
          kind: 'counterexample-closed',
          sourceKind,
          origin: 'counterexample',
          artifactPath: resolvedPath,
          detail,
          claimRefs: claimIds,
          generatorLineage: backend || 'counterexample',
        })
      : null;
  if (closureEvidence) {
    addEvidenceForClaims(claimStateMap, claimIds, closureEvidence, warnings, resolvedPath);
  }

  for (const claimId of claimIds) {
    const claimState = claimStateMap.get(claimId);
    if (!claimState) {
      pushWarning(
        warnings,
        'unknown-claim-ref',
        `Counterexample references unknown claim "${claimId}".`,
        { claimId, artifactPath: resolvedPath },
      );
      continue;
    }
    claimState.counterexamples.total += 1;
    if (triageStatus === 'resolved') {
      claimState.counterexamples.resolved += 1;
    } else if (triageStatus === 'accepted-risk') {
      claimState.counterexamples.acceptedRisk += 1;
    } else {
      claimState.counterexamples.open += 1;
    }
  }
};


const camelSecurityResult = (value) => {
  const raw = maybeString(value);
  if (raw === 'needs-human-review') return 'needsHumanReview';
  if (raw === 'out-of-scope') return 'outOfScope';
  return raw;
};

const reviewMapForSecurityFindings = (securityReviewPath) => {
  const reviews = new Map();
  if (!securityReviewPath) return reviews;
  const resolvedPath = ensureFile(securityReviewPath, 'Security review');
  const payload = readJson(resolvedPath);
  for (const [reviewIndex, review] of ensureArray(payload.reviews ?? [], `Security review reviews (${resolvedPath})`).entries()) {
    const findingId = maybeString(review?.findingId);
    if (!findingId) continue;
    const reviewEntry = { ...review, reviewIndex, artifactPath: resolvedPath };
    const existing = reviews.get(findingId) ?? [];
    existing.push(reviewEntry);
    reviews.set(findingId, existing);
  }
  return reviews;
};

const ensureSecurityClaimState = (claimStateMap, rawClaim) => {
  const claimId = maybeString(rawClaim?.id);
  if (!claimId) return null;
  if (!claimStateMap.has(claimId)) {
    claimStateMap.set(claimId, buildClaimState({
      id: claimId,
      statement: maybeString(rawClaim.statement) || `Security claim ${claimId}`,
      criticality: maybeString(rawClaim.criticality) || 'medium',
      targetLevel: maybeString(rawClaim.targetLevel) || 'A2',
      securityClaimType: normalizeSecurityClaimType(rawClaim.type),
      minIndependentSources: rawClaim.minIndependentSources,
      requiredLanes: Array.isArray(rawClaim.requiredLanes) ? rawClaim.requiredLanes : ['spec', 'adversarial'],
      requiredEvidenceKinds: Array.isArray(rawClaim.requiredEvidenceKinds) ? rawClaim.requiredEvidenceKinds : [],
    }));
  }
  const claimState = claimStateMap.get(claimId);
  const claimType = normalizeSecurityClaimType(rawClaim?.type);
  if (claimType) {
    claimState.securityClaimType = claimType;
  }
  return claimState;
};

const ingestSecurityClaims = (securityClaimsPath, claimStateMap, warnings) => {
  if (!securityClaimsPath) return new Set();
  const resolvedPath = ensureFile(securityClaimsPath, 'Security claims');
  const payload = readJson(resolvedPath);
  const claimIds = new Set();
  for (const [claimIndex, rawClaim] of ensureArray(payload.claims ?? [], `Security claims (${resolvedPath})`).entries()) {
    const claimState = ensureSecurityClaimState(claimStateMap, rawClaim);
    if (!claimState) continue;
    claimIds.add(claimState.claimId);
    const evidence = normalizeEvidenceEntry({
      lane: 'spec',
      kind: 'security-claim',
      sourceKind: 'spec-derived',
      origin: 'security-claim',
      status: 'observed',
      artifactPath: `${resolvedPath}#/claims/${claimIndex}`,
      detail: `Security claim imported from security-claim/v1 (type=${rawClaim.type ?? 'unknown'}).`,
      claimRefs: [claimState.claimId],
      generatorLineage: `security-claim/${rawClaim.provenance?.generator ?? 'unknown'}`,
    });
    addEvidenceForClaims(claimStateMap, [claimState.claimId], evidence, warnings, resolvedPath);
  }
  return claimIds;
};

const ingestSecurityFindingsAndReviews = (securityFindingsPath, securityReviewPath, claimStateMap, warnings) => {
  if (!securityFindingsPath) return;
  const resolvedPath = ensureFile(securityFindingsPath, 'Security findings');
  const payload = readJson(resolvedPath);
  const reviews = reviewMapForSecurityFindings(securityReviewPath);

  for (const [findingIndex, finding] of ensureArray(payload.findings ?? [], `Security findings (${resolvedPath})`).entries()) {
    const claimId = maybeString(finding?.claimId);
    const findingId = maybeString(finding?.id);
    if (!claimId || !findingId) continue;
    const findingReviews = reviews.get(findingId) ?? [];
    const review = findingReviews.at(-1);
    if (!claimStateMap.has(claimId)) {
      claimStateMap.set(claimId, buildClaimState({
        id: claimId,
        statement: `Security claim ${claimId}`,
        criticality: maybeString(finding.severity) || 'medium',
        targetLevel: 'A2',
        securityClaimType: normalizeSecurityClaimType(review?.claimType),
        requiredLanes: ['spec', 'adversarial'],
        requiredEvidenceKinds: [],
      }));
    }
    const claimState = claimStateMap.get(claimId);
    const reviewResult = maybeString(review?.result);
    const effectiveResult = reviewResult || maybeString(finding.status) || 'candidate';
    const severity = maybeString(review?.severity || finding.severity) || 'medium';
    const claimType = normalizeSecurityClaimType(review?.claimType) || claimState.securityClaimType;
    if (claimType) {
      claimState.securityClaimType = claimType;
    }
    const evidence = normalizeEvidenceEntry({
      lane: 'adversarial',
      kind: 'security-finding',
      sourceKind: 'source-derived',
      origin: 'security-finding',
      status: 'observed',
      artifactPath: `${resolvedPath}#/findings/${findingIndex}`,
      detail: `Security finding ${findingId}: status=${finding.status ?? 'unknown'}, severity=${severity}, review=${effectiveResult}${claimType ? `, claimType=${claimType}` : ''}.`,
      claimRefs: [claimId],
      generatorLineage: `security-finding/${finding.provenance?.generator ?? 'unknown'}`,
    });
    addEvidenceForClaims(claimStateMap, [claimId], evidence, warnings, resolvedPath);

    for (const reviewEntry of findingReviews) {
      const reviewEvidence = normalizeEvidenceEntry({
        lane: 'adversarial',
        kind: 'security-review',
        sourceKind: 'source-derived',
        origin: 'security-review',
        status: 'observed',
        artifactPath: `${reviewEntry.artifactPath}#/reviews/${reviewEntry.reviewIndex}`,
        detail: `Security review classified ${findingId} as ${reviewEntry.result ?? 'unknown'}${reviewEntry.falsePositiveRootCause ? ` (${reviewEntry.falsePositiveRootCause})` : ''}${reviewEntry.claimType ? `; claimType=${reviewEntry.claimType}` : ''}${reviewEntry.assumptionHandling?.mode ? `; assumptionHandling=${reviewEntry.assumptionHandling.mode}` : ''}.`,
        claimRefs: [claimId],
        generatorLineage: `security-review/${reviewEntry.reviewer ?? 'unknown'}`,
      });
      addEvidenceForClaims(claimStateMap, [claimId], reviewEvidence, warnings, reviewEntry.artifactPath);
    }

    claimState.counterexamples.total += 1;
    if (claimState.securityClaimType === 'assumption') {
      const handling = normalizeAssumptionHandling(review?.assumptionHandling, effectiveResult, findingId);
      claimState.assumptionHandling.push(handling);
    }
    if (effectiveResult === 'rejected' || effectiveResult === 'out-of-scope' || effectiveResult === 'waived') {
      claimState.counterexamples.resolved += 1;
    } else if (effectiveResult === 'accepted-risk') {
      claimState.counterexamples.acceptedRisk += 1;
    } else {
      claimState.counterexamples.open += 1;
    }

    const resultKey = camelSecurityResult(effectiveResult) || effectiveResult;
    if ((severity === 'high' || severity === 'critical') && (effectiveResult === 'candidate' || effectiveResult === 'needs-human-review' || effectiveResult === 'confirmed')) {
      pushWarning(
        warnings,
        'unresolved-critical-counterexample',
        `High/critical security finding ${findingId} remains ${resultKey}.`,
        { claimId, artifactPath: resolvedPath },
      );
    }
  }
};

const ingestEvidenceManifest = (manifestPath, claimStateMap, warnings) => {
  const resolvedPath = ensureFile(manifestPath, 'Evidence manifest');
  const manifest = readJson(resolvedPath);
  const entries = ensureArray(manifest.entries ?? [], `Evidence manifest entries (${resolvedPath})`);
  for (const entry of entries) {
    const normalized = normalizeEvidenceEntry({
      ...entry,
      origin: entry.origin || 'evidence-manifest',
    });
    if (normalized.claimRefs.length === 0) {
      pushWarning(
        warnings,
        'unrecognized-evidence-claim',
        'Evidence manifest entry must reference at least one claim.',
        { artifactPath: resolvedPath },
      );
      continue;
    }
    addEvidenceForClaims(claimStateMap, normalized.claimRefs, normalized, warnings, resolvedPath);
  }
};

const summarizeClaim = (claimState, warnings) => {
  const observedEvidence = claimState.evidence.filter((entry) => entry.status === 'observed');
  const observedLanes = sortLanes(observedEvidence.map((entry) => entry.lane));
  const observedEvidenceKinds = uniqueSorted(observedEvidence.map((entry) => entry.kind));
  const missingLanes = sortLanes(
    claimState.requiredLanes.filter((lane) => !observedLanes.includes(lane)),
  );
  const missingEvidenceKinds = uniqueSorted(
    claimState.requiredEvidenceKinds.filter((kind) => !observedEvidenceKinds.includes(kind)),
  );
  const observedSourceKinds = uniqueSorted(observedEvidence.map((entry) => entry.sourceKind));
  const observedIndependentSources = observedSourceKinds.length;
  const claimWarnings = [];

  if (observedEvidence.length > 0 && observedEvidence.every((entry) => entry.sourceKind === 'source-derived')) {
    claimWarnings.push('all-evidence-derived-from-source');
  }
  if (!observedEvidence.some((entry) => entry.sourceKind === 'spec-derived')) {
    claimWarnings.push('missing-spec-derived-evidence');
  }
  if (observedIndependentSources < claimState.minIndependentSources) {
    claimWarnings.push('insufficient-independent-lanes');
  }
  const generatorLineages = uniqueSorted(
    observedEvidence
      .map((entry) => entry.generatorLineage)
      .filter((value) => typeof value === 'string' && value.length > 0),
  );
  if (observedEvidence.length > 1 && generatorLineages.length === 1) {
    claimWarnings.push('same-generator-lineage');
  }
  if (
    (claimState.criticality === 'high' || claimState.criticality === 'critical') &&
    claimState.counterexamples.open > 0
  ) {
    claimWarnings.push('unresolved-critical-counterexample');
  }
  if (claimState.assumptionHandling.some((entry) => entry.mode === 'assumption-validation-required')) {
    claimWarnings.push('assumption-validation-required');
  }

  for (const code of claimWarnings) {
    const messages = {
      'all-evidence-derived-from-source': 'All observed evidence for this claim is source-derived.',
      'missing-spec-derived-evidence': 'No spec-derived evidence was observed for this claim.',
      'insufficient-independent-lanes': `Observed independent source kinds (${observedIndependentSources}) do not meet the minimum (${claimState.minIndependentSources}).`,
      'same-generator-lineage': 'Observed evidence appears to share a single generator lineage.',
      'unresolved-critical-counterexample': 'Critical claim still has unresolved counterexamples.',
      'assumption-validation-required': 'Assumption-derived security finding requires validation before vulnerability interpretation.',
    };
    pushWarning(warnings, code, messages[code], { claimId: claimState.claimId });
  }

  const status =
    missingLanes.length === 0 &&
    missingEvidenceKinds.length === 0 &&
    claimWarnings.length === 0
      ? 'satisfied'
      : 'warning';

  const summary = {
    claimId: claimState.claimId,
    statement: claimState.statement,
    criticality: claimState.criticality,
    targetLevel: claimState.targetLevel,
    minIndependentSources: claimState.minIndependentSources,
    observedIndependentSources,
    requiredLanes: claimState.requiredLanes,
    observedLanes,
    missingLanes,
    requiredEvidenceKinds: claimState.requiredEvidenceKinds,
    observedEvidenceKinds,
    missingEvidenceKinds,
    counterexamples: claimState.counterexamples,
    independenceWarnings: uniqueSorted(claimWarnings),
    status,
    evidence: observedEvidence.sort((left, right) => {
      const laneCompare = LANE_ORDER.indexOf(left.lane) - LANE_ORDER.indexOf(right.lane);
      if (laneCompare !== 0) return laneCompare;
      return left.kind.localeCompare(right.kind);
    }),
  };
  if (claimState.securityClaimType) {
    summary.securityClaimType = claimState.securityClaimType;
  }
  if (claimState.assumptionHandling.length > 0) {
    summary.assumptionHandling = claimState.assumptionHandling
      .map((entry) => ({
        mode: entry.mode,
        findingId: entry.findingId,
        reviewResult: entry.reviewResult,
        rationale: entry.rationale,
        evidenceRefs: entry.evidenceRefs,
      }))
      .sort((left, right) => `${left.findingId}:${left.mode}`.localeCompare(`${right.findingId}:${right.mode}`));
  }
  return summary;
};

const buildLaneCoverage = (claimSummaries) => {
  const coverage = {};
  for (const lane of LANE_ORDER) {
    coverage[lane] = {
      requiredClaims: claimSummaries.filter((claim) => claim.requiredLanes.includes(lane)).length,
      observedClaims: claimSummaries.filter((claim) => claim.observedLanes.includes(lane)).length,
    };
  }
  return coverage;
};

const buildMarkdown = (summary) => {
  const headerLines = [
    '# Assurance Summary',
    '',
    `- generatedAt: ${summary.generatedAt}`,
    `- claimCount: ${summary.summary.claimCount}`,
    `- satisfiedClaims: ${summary.summary.satisfiedClaims}`,
    `- warningClaims: ${summary.summary.warningClaims}`,
    `- warningCount: ${summary.summary.warningCount}`,
    `- unlinkedCounterexamples: ${summary.summary.unlinkedCounterexamples}`,
    '',
  ];

  const reviewSurfaceLines = [];
  if (summary.reviewSurface) {
    const surface = summary.reviewSurface;
    reviewSurfaceLines.push(
      '## Reviewer decision surface',
      '',
      `- recommendedReviewerAction: ${surface.recommendedReviewerAction.action}`,
      `- reason: ${surface.recommendedReviewerAction.reason}`,
      `- manifestClaims: satisfied=${surface.summary.manifestClaimStatusCounts.satisfied}, partial=${surface.summary.manifestClaimStatusCounts.partial}, waived=${surface.summary.manifestClaimStatusCounts.waived}, unresolved=${surface.summary.manifestClaimStatusCounts.unresolved}, failed=${surface.summary.manifestClaimStatusCounts.failed}`,
      `- assuranceSummaryClaims: satisfied=${surface.summary.assuranceClaimStatusCounts.satisfied}, warning=${surface.summary.assuranceClaimStatusCounts.warning}`,
      `- missingEvidenceClaims: ${surface.summary.missingEvidenceClaims}`,
      `- activeWaivers: ${surface.summary.activeWaivers}`,
      `- producerSignals: ${surface.producerSignals.status} (reportOnlyFindings=${surface.producerSignals.reportOnlyFindings}, missingEvidence=${surface.producerSignals.missingEvidence})`,
      `- boundaryMap: ${surface.boundaryMap.status} (findings=${surface.boundaryMap.totalFindings})`,
      `- policyDecision: ${surface.policyDecision.result ?? 'not-provided'} (mode=${surface.policyDecision.mode ?? 'n/a'})`,
      '',
      'Interpretation notes:',
      '',
      ...surface.interpretationNotes.map((note) => `- ${note}`),
      '',
    );
    if (surface.claimEvidence.missingEvidenceClaims.length > 0) {
      reviewSurfaceLines.push(
        '### Missing claim evidence',
        '',
        renderTable(
          ['claim', 'status', 'missing evidence refs'],
          surface.claimEvidence.missingEvidenceClaims.map((claim) => [
            claim.claimId,
            claim.status,
            claim.missingEvidenceRefs.join(', '),
          ]),
        ),
        '',
      );
    }
    if (surface.claimEvidence.unresolvedClaims.length > 0) {
      reviewSurfaceLines.push(
        '### Unresolved claims',
        '',
        renderTable(
          ['claim', 'status', 'reason'],
          surface.claimEvidence.unresolvedClaims.map((claim) => [
            claim.claimId,
            claim.status,
            claim.reason,
          ]),
        ),
        '',
      );
    }
    if (surface.waivers.waiverRefs.length > 0) {
      reviewSurfaceLines.push(
        '### Waivers',
        '',
        renderTable(
          ['claim', 'waiver', 'status', 'owner', 'expires', 'source'],
          surface.waivers.waiverRefs.map((waiver) => [
            waiver.claimId,
            waiver.id,
            waiver.status,
            waiver.owner ?? 'n/a',
            waiver.expires ?? 'n/a',
            waiver.source,
          ]),
        ),
        '',
      );
    }
    if (surface.boundaryMap.reviewEvidence.length > 0) {
      reviewSurfaceLines.push(
        '### Boundary Map evidence',
        '',
        renderTable(
          ['type', 'severity', 'file', 'slice', 'ref', 'expected owner', 'observed dependency'],
          surface.boundaryMap.reviewEvidence.map((entry) => [
            entry.type,
            entry.severity,
            entry.file,
            entry.slice ?? 'n/a',
            entry.ref ?? 'n/a',
            entry.expectedOwner,
            entry.observedDependency,
          ]),
        ),
        '',
      );
    }
  }

  const lines = [
    ...headerLines,
    ...reviewSurfaceLines,
    '## Claim status',
    '',
    renderTable(
      ['claim', 'type', 'status', 'required lanes', 'observed lanes', 'missing lanes', 'assumption handling', 'warnings'],
      summary.claims.map((claim) => [
        claim.claimId,
        claim.securityClaimType ?? 'n/a',
        claim.status,
        claim.requiredLanes.join(', '),
        claim.observedLanes.join(', '),
        claim.missingLanes.join(', '),
        (claim.assumptionHandling ?? []).map((entry) => `${entry.findingId}:${entry.mode}`).join(', ') || 'n/a',
        claim.independenceWarnings.join(', '),
      ]),
    ),
    '',
    '## Lane coverage',
    '',
    renderTable(
      ['lane', 'required claims', 'observed claims'],
      LANE_ORDER.map((lane) => [
        lane,
        String(summary.laneCoverage[lane].requiredClaims),
        String(summary.laneCoverage[lane].observedClaims),
      ]),
    ),
  ];

  if (summary.warnings.length > 0) {
    lines.push('', '## Warnings', '');
    for (const warning of summary.warnings) {
      const claimPart = warning.claimId ? ` claim=${warning.claimId}` : '';
      const artifactPart = warning.artifactPath ? ` artifact=${warning.artifactPath}` : '';
      lines.push(`- ${warning.code}:${claimPart}${artifactPart} ${warning.message}`.trim());
    }
  }

  return `${lines.join('\n')}\n`;
};

export const run = (argv = process.argv.slice(2)) => {
  const options = parseArgs(argv);
  const warnings = [];
  const topLevelState = { unlinkedCounterexamples: 0 };

  const assuranceProfilePath = ensureFile(options.assuranceProfile, 'Assurance profile');
  const producerSummaryInputs = readOptionalJsonInputs(options.producerSummaries, 'Producer summary');
  const boundaryMapSummaryInputs = readOptionalJsonInputs(options.boundaryMapSummaries, 'Boundary Map summary');
  const claimEvidenceManifestInputs = readOptionalJsonInputs(
    options.claimEvidenceManifests,
    'Claim evidence manifest',
  );
  const policyDecisionInput = options.policyDecision
    ? readOptionalJsonInputs([options.policyDecision], 'Policy decision')[0]
    : null;
  const assuranceProfile = readJson(assuranceProfilePath);
  const claims = ensureArray(assuranceProfile.claims ?? [], 'assurance profile claims');
  const claimIds = claims.map((claim) => maybeString(claim?.id));
  const duplicateClaimIds = uniqueSorted(
    claimIds.filter((claimId, index) => claimId && claimIds.indexOf(claimId) !== index),
  );
  if (duplicateClaimIds.length > 0) {
    throw new Error(`Assurance profile contains duplicate claim ids: ${duplicateClaimIds.join(', ')}`);
  }
  const claimStateMap = new Map(claims.map((claim) => [claim.id, buildClaimState(claim)]));

  ingestSecurityClaims(options.securityClaims, claimStateMap, warnings);

  const contextPackRefs = collectContextPackReferences(
    options.contextPacks,
    maybeString(assuranceProfile.profileId),
    claimStateMap,
    warnings,
  );

  ingestVerifyLiteSummary(options.verifyLiteSummary, claimStateMap, contextPackRefs, warnings);
  for (const formalSummaryPath of options.formalSummaries) {
    ingestFormalSummary(formalSummaryPath, claimStateMap, contextPackRefs, warnings);
  }
  ingestConformanceReport(options.conformanceReport, claimStateMap, contextPackRefs, warnings);
  ingestSecurityFindingsAndReviews(options.securityFindings, options.securityReview, claimStateMap, warnings);
  for (const counterexamplePath of options.counterexamples) {
    ingestCounterexample(counterexamplePath, claimStateMap, warnings, topLevelState);
  }
  for (const manifestPath of options.evidenceManifests) {
    ingestEvidenceManifest(manifestPath, claimStateMap, warnings);
  }

  const claimSummaries = Array.from(claimStateMap.values())
    .map((claimState) => summarizeClaim(claimState, warnings))
    .sort((left, right) => left.claimId.localeCompare(right.claimId));

  const summary = {
    schemaVersion: 'assurance-summary/v1',
    generatedAt: new Date().toISOString(),
    metadata: buildArtifactMetadata(),
    inputs: {
      assuranceProfile: assuranceProfilePath,
      contextPacks: uniqueSorted(options.contextPacks.map((targetPath) => path.resolve(targetPath))),
      verifyLiteSummary: options.verifyLiteSummary ? path.resolve(options.verifyLiteSummary) : null,
      formalSummaries: uniqueSorted(options.formalSummaries.map((targetPath) => path.resolve(targetPath))),
      conformanceReport: options.conformanceReport ? path.resolve(options.conformanceReport) : null,
      counterexamples: uniqueSorted(options.counterexamples.map((targetPath) => path.resolve(targetPath))),
      evidenceManifests: uniqueSorted(options.evidenceManifests.map((targetPath) => path.resolve(targetPath))),
      producerSummaries: uniqueSorted(options.producerSummaries.map((targetPath) => path.resolve(targetPath))),
      boundaryMapSummaries: uniqueSorted(options.boundaryMapSummaries.map((targetPath) => path.resolve(targetPath))),
      claimEvidenceManifests: uniqueSorted(options.claimEvidenceManifests.map((targetPath) => path.resolve(targetPath))),
      policyDecision: options.policyDecision ? path.resolve(options.policyDecision) : null,
      securityClaims: options.securityClaims ? path.resolve(options.securityClaims) : null,
      securityFindings: options.securityFindings ? path.resolve(options.securityFindings) : null,
      securityReview: options.securityReview ? path.resolve(options.securityReview) : null,
    },
    summary: {
      claimCount: claimSummaries.length,
      satisfiedClaims: claimSummaries.filter((claim) => claim.status === 'satisfied').length,
      warningClaims: claimSummaries.filter((claim) => claim.status === 'warning').length,
      claimsMissingRequiredLanes: claimSummaries.filter((claim) => claim.missingLanes.length > 0).length,
      claimsMissingRequiredEvidenceKinds: claimSummaries.filter((claim) => claim.missingEvidenceKinds.length > 0)
        .length,
      unlinkedCounterexamples: topLevelState.unlinkedCounterexamples,
      warningCount: warnings.length,
    },
    laneCoverage: buildLaneCoverage(claimSummaries),
    claims: claimSummaries,
    warnings,
  };
  summary.reviewSurface = buildReviewSurface({
    summary,
    options,
    producerSummaryInputs,
    boundaryMapSummaryInputs,
    claimEvidenceManifestInputs,
    policyDecisionInput,
  });

  writeFile(options.outputJson, `${JSON.stringify(summary, null, 2)}\n`);
  writeFile(options.outputMd, buildMarkdown(summary));
  console.log(
    `[assurance] wrote summary: claims=${summary.summary.claimCount} warnings=${summary.summary.warningCount} json=${path.resolve(options.outputJson)}`,
  );
  return summary;
};

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  try {
    run();
  } catch (error) {
    console.error(`[assurance] ${error instanceof Error ? error.message : String(error)}`);
    process.exit(1);
  }
}
