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
]);

const usage = () => {
  console.log(`Usage: node scripts/assurance/aggregate-lanes.mjs --assurance-profile <path> [options]

Options:
  --context-pack <path>          Context Pack v1 input. Repeatable.
  --verify-lite-summary <path>   Verify Lite summary JSON.
  --formal-summary <path>        Formal summary v1/v2 JSON. Repeatable.
  --conformance-report <path>    Conformance report JSON.
  --counterexample <path>        Counterexample JSON. Repeatable.
  --evidence-manifest <path>     Supplemental evidence manifest JSON. Repeatable.
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

  for (const code of claimWarnings) {
    const messages = {
      'all-evidence-derived-from-source': 'All observed evidence for this claim is source-derived.',
      'missing-spec-derived-evidence': 'No spec-derived evidence was observed for this claim.',
      'insufficient-independent-lanes': `Observed independent source kinds (${observedIndependentSources}) do not meet the minimum (${claimState.minIndependentSources}).`,
      'same-generator-lineage': 'Observed evidence appears to share a single generator lineage.',
      'unresolved-critical-counterexample': 'Critical claim still has unresolved counterexamples.',
    };
    pushWarning(warnings, code, messages[code], { claimId: claimState.claimId });
  }

  const status =
    missingLanes.length === 0 &&
    missingEvidenceKinds.length === 0 &&
    claimWarnings.length === 0
      ? 'satisfied'
      : 'warning';

  return {
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
  const lines = [
    '# Assurance Summary',
    '',
    `- generatedAt: ${summary.generatedAt}`,
    `- claimCount: ${summary.summary.claimCount}`,
    `- satisfiedClaims: ${summary.summary.satisfiedClaims}`,
    `- warningClaims: ${summary.summary.warningClaims}`,
    `- warningCount: ${summary.summary.warningCount}`,
    `- unlinkedCounterexamples: ${summary.summary.unlinkedCounterexamples}`,
    '',
    '## Claim status',
    '',
    renderTable(
      ['claim', 'status', 'required lanes', 'observed lanes', 'missing lanes', 'warnings'],
      summary.claims.map((claim) => [
        claim.claimId,
        claim.status,
        claim.requiredLanes.join(', '),
        claim.observedLanes.join(', '),
        claim.missingLanes.join(', '),
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
