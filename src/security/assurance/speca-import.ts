import { existsSync, promises as fs } from 'node:fs';
import { createRequire } from 'node:module';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { normalizeArtifactPath } from '../../utils/path-normalization.js';

const require = createRequire(import.meta.url);
const Ajv2020 = require('ajv/dist/2020.js') as new (options?: JsonRecord) => {
  compile: (schema: unknown) => ((data: unknown) => boolean) & { errors?: unknown };
};
const addFormats = require('ajv-formats') as (ajv: unknown) => void;

export interface ImportWarning {
  code: string;
  source: string;
  path: string;
  message: string;
}

export interface SpecaImportOptions {
  generatedAt?: string;
  repoRoot?: string;
  validate?: boolean;
}

export interface SpecaImportOutputPaths {
  claims: string;
  threatModel: string;
  findings: string;
  review: string;
  summaryJson: string;
  summaryMarkdown: string;
}

export interface SpecaImportResult {
  generatedAt: string;
  artifacts: SecurityArtifactSet;
  warnings: ImportWarning[];
  outputPaths: SpecaImportOutputPaths;
}

type JsonRecord = Record<string, unknown>;

type SecurityClaimDocument = {
  schemaVersion: 'security-claim/v1';
  generatedAt: string;
  claims: JsonRecord[];
  summary: {
    totalClaims: number;
    byCriticality: Record<'low' | 'medium' | 'high' | 'critical', number>;
  };
};

type SecurityThreatModelDocument = {
  schemaVersion: 'security-threat-model/v1';
  generatedAt: string;
  frameworks: Array<'STRIDE' | 'CWE_TOP_25'>;
  threats: JsonRecord[];
  summary: { totalThreats: number };
};

type SecurityFindingDocument = {
  schemaVersion: 'security-finding/v1';
  generatedAt: string;
  findings: JsonRecord[];
  summary: {
    totalFindings: number;
    byStatus: Record<'candidate' | 'needsHumanReview' | 'confirmed' | 'rejected' | 'waived' | 'outOfScope', number>;
    bySeverity: Record<'low' | 'medium' | 'high' | 'critical', number>;
  };
};

type SecurityReviewDocument = {
  schemaVersion: 'security-review/v1';
  generatedAt: string;
  reviews: JsonRecord[];
  summary: {
    totalReviews: number;
    byResult: Record<'needsHumanReview' | 'confirmed' | 'rejected' | 'waived' | 'outOfScope', number>;
    falsePositiveRootCauses: Record<
      'deadCode' | 'trustBoundaryMisunderstanding' | 'outOfScope' | 'codeReadingError' | 'specMisinterpretation' | 'insufficientEvidence',
      number
    >;
  };
};

export interface SecurityArtifactSet {
  claims: SecurityClaimDocument;
  threatModel: SecurityThreatModelDocument;
  findings: SecurityFindingDocument;
  review: SecurityReviewDocument;
}

export type SpecaLikeBundle = {
  properties: JsonRecord[];
  threats: JsonRecord[];
  findings: JsonRecord[];
  reviews: JsonRecord[];
  sourceFiles: Record<'properties' | 'threats' | 'findings' | 'reviews', string>;
  warnings: ImportWarning[];
};

const GENERATOR = 'speca-compatible-import';
const MODULE_DIR = path.dirname(fileURLToPath(import.meta.url));

const STRIDE_VALUES = [
  'Spoofing',
  'Tampering',
  'Repudiation',
  'Information Disclosure',
  'Denial of Service',
  'Elevation of Privilege',
] as const;

const REQUIRED_LANES = ['spec', 'behavior', 'adversarial', 'model', 'proof', 'runtime'] as const;
const CLAIM_TYPES = ['invariant', 'precondition', 'postcondition', 'assumption'] as const;
const SEVERITIES = ['low', 'medium', 'high', 'critical'] as const;
const CONFIDENCE = ['low', 'medium', 'high'] as const;
const FINDING_STATUSES = ['candidate', 'needs-human-review', 'confirmed', 'rejected', 'waived', 'out-of-scope'] as const;
const REVIEW_RESULTS = ['needs-human-review', 'confirmed', 'rejected', 'waived', 'out-of-scope'] as const;
const GATE_RESULTS = ['pass', 'fail', 'unknown', 'not-applicable'] as const;
const FALSE_POSITIVE_ROOT_CAUSES = [
  'dead-code',
  'trust-boundary-misunderstanding',
  'out-of-scope',
  'code-reading-error',
  'spec-misinterpretation',
  'insufficient-evidence',
] as const;

type Criticality = (typeof SEVERITIES)[number];
type FindingStatus = (typeof FINDING_STATUSES)[number];
type ReviewResult = (typeof REVIEW_RESULTS)[number];
type FalsePositiveRootCause = (typeof FALSE_POSITIVE_ROOT_CAUSES)[number];

const countCriticality = (): Record<Criticality, number> => ({ low: 0, medium: 0, high: 0, critical: 0 });
const countFindingStatus = () => ({ candidate: 0, needsHumanReview: 0, confirmed: 0, rejected: 0, waived: 0, outOfScope: 0 });
const countReviewResult = () => ({ needsHumanReview: 0, confirmed: 0, rejected: 0, waived: 0, outOfScope: 0 });
const countRootCause = () => ({
  deadCode: 0,
  trustBoundaryMisunderstanding: 0,
  outOfScope: 0,
  codeReadingError: 0,
  specMisinterpretation: 0,
  insufficientEvidence: 0,
});

function isRecord(value: unknown): value is JsonRecord {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function asString(value: unknown): string | undefined {
  return typeof value === 'string' && value.trim().length > 0 ? value.trim() : undefined;
}

function asStringArray(value: unknown): string[] {
  if (Array.isArray(value)) {
    return value.map(asString).filter((entry): entry is string => Boolean(entry));
  }
  const single = asString(value);
  return single ? [single] : [];
}

function unique(values: string[]): string[] {
  return [...new Set(values)];
}

function formatId(prefix: string, index: number): string {
  return `${prefix}-${String(index + 1).padStart(3, '0')}`;
}

function warning(warnings: ImportWarning[], code: string, source: string, pathRef: string, message: string): void {
  warnings.push({ code, source, path: pathRef, message });
}

function warnUnknownFields(
  warnings: ImportWarning[],
  source: string,
  pathRef: string,
  record: JsonRecord,
  knownFields: ReadonlySet<string>,
): void {
  for (const key of Object.keys(record).sort()) {
    if (!knownFields.has(key)) {
      warning(warnings, 'unsupported-field', source, `${pathRef}/${key}`, `Unsupported SPECA-like field '${key}' was preserved as an import warning.`);
    }
  }
}

function normalizeEnum<T extends readonly string[]>(
  value: unknown,
  allowed: T,
  fallback: T[number],
  warnings: ImportWarning[],
  source: string,
  pathRef: string,
  label: string,
): T[number] {
  const candidate = asString(value)?.toLowerCase();
  if (candidate) {
    const exact = allowed.find((entry) => entry.toLowerCase() === candidate);
    if (exact) {
      return exact as T[number];
    }
  }
  warning(warnings, 'unsupported-value', source, pathRef, `Unsupported ${label}; defaulted to '${fallback}'.`);
  return fallback;
}

function normalizeStride(value: unknown, warnings: ImportWarning[], source: string, pathRef: string): string | undefined {
  const candidate = asString(value);
  if (!candidate) {
    return undefined;
  }
  const normalized = candidate.toLowerCase().replace(/[\s_-]+/g, ' ');
  const aliases: Record<string, (typeof STRIDE_VALUES)[number]> = {
    spoofing: 'Spoofing',
    tampering: 'Tampering',
    repudiation: 'Repudiation',
    'information disclosure': 'Information Disclosure',
    'denial of service': 'Denial of Service',
    'elevation of privilege': 'Elevation of Privilege',
  };
  const mapped = aliases[normalized];
  if (mapped) {
    return mapped;
  }
  warning(warnings, 'unsupported-stride', source, pathRef, `Unsupported STRIDE tag '${candidate}' was not emitted.`);
  return undefined;
}

function normalizeStrideArray(value: unknown, warnings: ImportWarning[], source: string, pathRef: string): string[] {
  const values = asStringArray(value)
    .map((entry, index) => normalizeStride(entry, warnings, source, `${pathRef}/${index}`))
    .filter((entry): entry is string => Boolean(entry));
  return unique(values);
}

function normalizeCwe(value: unknown, warnings: ImportWarning[], source: string, pathRef: string): string | undefined {
  const candidate = asString(value);
  if (!candidate) {
    return undefined;
  }
  const match = candidate.toUpperCase().match(/CWE[-\s]?([0-9]+)/);
  if (match?.[1]) {
    return `CWE-${match[1]}`;
  }
  warning(warnings, 'unsupported-cwe', source, pathRef, `Unsupported CWE tag '${candidate}' was not emitted.`);
  return undefined;
}

function normalizeCweArray(value: unknown, warnings: ImportWarning[], source: string, pathRef: string): string[] {
  const values = asStringArray(value)
    .map((entry, index) => normalizeCwe(entry, warnings, source, `${pathRef}/${index}`))
    .filter((entry): entry is string => Boolean(entry));
  return unique(values);
}

function normalizeAssuranceLevel(value: unknown, warnings: ImportWarning[], source: string, pathRef: string): string {
  const candidate = asString(value)?.toUpperCase();
  if (candidate && /^A[0-4]$/.test(candidate)) {
    return candidate;
  }
  warning(warnings, 'unsupported-assurance-level', source, pathRef, "Unsupported assurance level; defaulted to 'A2'.");
  return 'A2';
}

function nextAvailableId(prefix: string, usedIds: Set<string>, reservedIds: Set<string> = new Set()): string {
  for (let index = 0; index < Number.MAX_SAFE_INTEGER; index += 1) {
    const candidate = formatId(prefix, index);
    if (!usedIds.has(candidate) && !reservedIds.has(candidate)) {
      return candidate;
    }
  }
  throw new Error(`Unable to allocate a unique ${prefix} id.`);
}

function claimIdFor(
  property: JsonRecord,
  index: number,
  usedIds: Set<string>,
  warnings: ImportWarning[],
  source: string,
  pathRef: string,
  reservedIds: Set<string> = new Set(),
): string {
  const raw = asString(property['id']);
  const candidate = raw?.startsWith('SEC-CLAIM-') ? raw : formatId('SEC-CLAIM', index);
  if (!usedIds.has(candidate) && (raw?.startsWith('SEC-CLAIM-') || !reservedIds.has(candidate))) {
    usedIds.add(candidate);
    return candidate;
  }
  const replacement = nextAvailableId('SEC-CLAIM', usedIds, reservedIds);
  usedIds.add(replacement);
  warning(
    warnings,
    'id-collision-normalized',
    source,
    pathRef,
    `Security claim id '${candidate}' collided during import and was normalized to '${replacement}'.`,
  );
  return replacement;
}

function findingIdFor(
  finding: JsonRecord,
  index: number,
  usedIds: Set<string>,
  warnings: ImportWarning[],
  source: string,
  pathRef: string,
  reservedIds: Set<string> = new Set(),
): string {
  const raw = asString(finding['id']);
  const candidate = raw?.startsWith('SEC-FINDING-') ? raw : formatId('SEC-FINDING', index);
  if (!usedIds.has(candidate) && (raw?.startsWith('SEC-FINDING-') || !reservedIds.has(candidate))) {
    usedIds.add(candidate);
    return candidate;
  }
  const replacement = nextAvailableId('SEC-FINDING', usedIds, reservedIds);
  usedIds.add(replacement);
  warning(
    warnings,
    'id-collision-normalized',
    source,
    pathRef,
    `Security finding id '${candidate}' collided during import and was normalized to '${replacement}'.`,
  );
  return replacement;
}

function sourceRefFor(property: JsonRecord, warnings: ImportWarning[], source: string, pathRef: string): JsonRecord[] {
  const sourceRefs = property['sourceRefs'];
  if (Array.isArray(sourceRefs) && sourceRefs.every(isRecord)) {
    return sourceRefs.map((entry, index) => ({
      kind: normalizeEnum(entry['kind'], ['spec', 'design', 'bug-bounty-scope', 'issue', 'security-policy', 'other'] as const, 'spec', warnings, source, `${pathRef}/sourceRefs/${index}/kind`, 'sourceRef kind'),
      uri: asString(entry['uri']) ?? 'speca-like:unknown-source',
      ...(asString(entry['section']) ? { section: asString(entry['section']) } : {}),
      ...(asString(entry['description']) ? { description: asString(entry['description']) } : {}),
    }));
  }

  const sourceObject = isRecord(property['source']) ? property['source'] : {};
  if (isRecord(property['source'])) {
    warnUnknownFields(warnings, source, `${pathRef}/source`, sourceObject, new Set(['kind', 'uri', 'section', 'description']));
  }
  return [
    {
      kind: normalizeEnum(sourceObject['kind'], ['spec', 'design', 'bug-bounty-scope', 'issue', 'security-policy', 'other'] as const, 'spec', warnings, source, `${pathRef}/source/kind`, 'sourceRef kind'),
      uri: asString(sourceObject['uri']) ?? asString(property['sourceUri']) ?? 'speca-like:unknown-source',
      ...(asString(sourceObject['section']) ? { section: asString(sourceObject['section']) } : {}),
      ...(asString(sourceObject['description']) ? { description: asString(sourceObject['description']) } : {}),
    },
  ];
}

function trustBoundaryFor(property: JsonRecord, warnings: ImportWarning[], source: string, pathRef: string): JsonRecord {
  const trustBoundary = isRecord(property['trustBoundary']) ? property['trustBoundary'] : {};
  if (isRecord(property['trustBoundary'])) {
    warnUnknownFields(
      warnings,
      source,
      `${pathRef}/trustBoundary`,
      trustBoundary,
      new Set(['id', 'boundaryIds', 'entryPoints', 'attackerControlled', 'dataClasses', 'notes']),
    );
  }
  const boundaryIds = unique([...asStringArray(trustBoundary['boundaryIds']), ...asStringArray(trustBoundary['id'])]);
  const entryPoints = unique(asStringArray(trustBoundary['entryPoints']));
  const dataClasses = unique(asStringArray(trustBoundary['dataClasses']));

  return {
    ...(boundaryIds.length > 0 ? { boundaryIds } : { boundaryIds: ['TB-IMPORTED'] }),
    entryPoints: entryPoints.length > 0 ? entryPoints : ['imported-entry-point'],
    attackerControlled: typeof trustBoundary['attackerControlled'] === 'boolean' ? trustBoundary['attackerControlled'] : true,
    ...(dataClasses.length > 0 ? { dataClasses } : {}),
    ...(asStringArray(trustBoundary['notes']).length > 0 ? { notes: asStringArray(trustBoundary['notes']) } : {}),
  };
}

function requiredLanesFor(value: unknown, warnings: ImportWarning[], source: string, pathRef: string): string[] {
  const lanes = asStringArray(value).filter((lane) => {
    const allowed = (REQUIRED_LANES as readonly string[]).includes(lane);
    if (!allowed) {
      warning(warnings, 'unsupported-lane', source, pathRef, `Unsupported required lane '${lane}' was not emitted.`);
    }
    return allowed;
  });
  return unique(lanes).length > 0 ? unique(lanes) : ['spec', 'adversarial', 'behavior'];
}

function relatedClaimIdsFor(
  threat: JsonRecord,
  propertyIdToClaimId: Map<string, string>,
  warnings: ImportWarning[],
  source: string,
  pathRef: string,
): string[] {
  const rawRefs = unique([
    ...asStringArray(threat['relatedClaimIds']),
    ...asStringArray(threat['relatedPropertyIds']),
    ...asStringArray(threat['propertyId']),
    ...asStringArray(threat['claimId']),
  ]);
  const mapped = rawRefs.map((ref) => propertyIdToClaimId.get(ref) ?? ref);
  if (mapped.length === 0) {
    const fallback = [...propertyIdToClaimId.values()][0];
    if (fallback) {
      warning(warnings, 'missing-related-claim', source, pathRef, `Threat was missing a claim/property reference; defaulted to '${fallback}'.`);
      return [fallback];
    }
  }
  return unique(mapped);
}

function normalizeStatus(value: unknown, warnings: ImportWarning[], source: string, pathRef: string): FindingStatus {
  return normalizeEnum(value, FINDING_STATUSES, 'candidate', warnings, source, pathRef, 'finding status') as FindingStatus;
}

function normalizeReviewResult(value: unknown, warnings: ImportWarning[], source: string, pathRef: string): ReviewResult {
  return normalizeEnum(value, REVIEW_RESULTS, 'needs-human-review', warnings, source, pathRef, 'review result') as ReviewResult;
}

function statusSummaryKey(status: string): keyof SecurityFindingDocument['summary']['byStatus'] {
  if (status === 'needs-human-review') return 'needsHumanReview';
  if (status === 'out-of-scope') return 'outOfScope';
  return status as keyof SecurityFindingDocument['summary']['byStatus'];
}

function reviewSummaryKey(result: string): keyof SecurityReviewDocument['summary']['byResult'] {
  if (result === 'needs-human-review') return 'needsHumanReview';
  if (result === 'out-of-scope') return 'outOfScope';
  return result as keyof SecurityReviewDocument['summary']['byResult'];
}

function rootCauseSummaryKey(rootCause: string): keyof SecurityReviewDocument['summary']['falsePositiveRootCauses'] {
  const mapping: Record<string, keyof SecurityReviewDocument['summary']['falsePositiveRootCauses']> = {
    'dead-code': 'deadCode',
    'trust-boundary-misunderstanding': 'trustBoundaryMisunderstanding',
    'out-of-scope': 'outOfScope',
    'code-reading-error': 'codeReadingError',
    'spec-misinterpretation': 'specMisinterpretation',
    'insufficient-evidence': 'insufficientEvidence',
  };
  return mapping[rootCause] ?? 'insufficientEvidence';
}

function normalizeFindingSeverity(value: unknown, warnings: ImportWarning[], source: string, pathRef: string): Criticality {
  return normalizeEnum(value, SEVERITIES, 'medium', warnings, source, pathRef, 'severity') as Criticality;
}

function normalizeConfidence(value: unknown, warnings: ImportWarning[], source: string, pathRef: string): string {
  return normalizeEnum(value, CONFIDENCE, 'medium', warnings, source, pathRef, 'confidence');
}

function affectedLocationsFor(finding: JsonRecord, warnings: ImportWarning[], source: string, pathRef: string): JsonRecord[] {
  const rawLocations = Array.isArray(finding['affectedLocations'])
    ? finding['affectedLocations']
    : Array.isArray(finding['locations'])
      ? finding['locations']
      : isRecord(finding['location'])
        ? [finding['location']]
        : [];

  if (rawLocations.length === 0) {
    warning(warnings, 'missing-location', source, pathRef, 'Finding was missing an affected location; emitted an imported placeholder location.');
    return [{ path: 'imported/unknown', startLine: 1, endLine: 1, description: 'Placeholder imported location.' }];
  }

  return rawLocations.map((raw, index) => {
    const location = isRecord(raw) ? raw : {};
    if (isRecord(raw)) {
      warnUnknownFields(warnings, source, `${pathRef}/affectedLocations/${index}`, location, new Set(['path', 'startLine', 'endLine', 'line', 'symbol', 'description']));
    }
    const startLine = typeof location['startLine'] === 'number'
      ? Math.max(1, Math.floor(location['startLine']))
      : typeof location['line'] === 'number'
        ? Math.max(1, Math.floor(location['line']))
        : 1;
    const rawEndLine = typeof location['endLine'] === 'number' ? Math.max(1, Math.floor(location['endLine'])) : startLine;
    const endLine = rawEndLine < startLine ? startLine : rawEndLine;
    if (rawEndLine < startLine) {
      warning(warnings, 'location-range-normalized', source, `${pathRef}/affectedLocations/${index}/endLine`, 'Affected location endLine was before startLine and was normalized.');
    }
    return {
      path: asString(location['path']) ?? 'imported/unknown',
      startLine,
      endLine,
      ...(asString(location['symbol']) ? { symbol: asString(location['symbol']) } : {}),
      ...(asString(location['description']) ? { description: asString(location['description']) } : {}),
    };
  });
}

function proofAttemptFor(finding: JsonRecord, claimId: string): JsonRecord {
  const proofAttempt = isRecord(finding['proofAttempt']) ? finding['proofAttempt'] : {};
  return {
    claim: asString(proofAttempt['claim']) ?? claimId,
    map: asString(proofAttempt['map']) ?? asString(finding['map']) ?? 'Imported SPECA-like audit map was not provided.',
    prove: asString(proofAttempt['prove']) ?? asString(finding['prove']) ?? 'Imported SPECA-like proof attempt did not establish the claim.',
    stressTest: asString(proofAttempt['stressTest']) ?? asString(finding['stressTest']) ?? asString(finding['counterexample']) ?? 'No counterexample was supplied by the SPECA-like fixture.',
    ...(asString(proofAttempt['report']) || asString(finding['report']) ? { report: asString(proofAttempt['report']) ?? asString(finding['report']) } : {}),
  };
}

function evidenceRefsFor(
  finding: JsonRecord,
  sourceFile: string,
  sourceId: string | undefined,
  warnings: ImportWarning[],
  pathRef: string,
): JsonRecord[] {
  const refs = Array.isArray(finding['evidenceRefs']) && finding['evidenceRefs'].every(isRecord)
    ? finding['evidenceRefs'].map((entry, index) => {
        warnUnknownFields(
          warnings,
          sourceFile,
          `${pathRef}/evidenceRefs/${index}`,
          entry,
          new Set(['id', 'kind', 'path', 'description']),
        );
        return {
          id: asString(entry['id']) ?? `SPEC-EVIDENCE-${String(index + 1).padStart(3, '0')}`,
          kind: normalizeEnum(
            entry['kind'],
            ['security-claim', 'security-code-map', 'audit-task', 'source', 'trace', 'manual', 'other'] as const,
            'source',
            warnings,
            sourceFile,
            `${pathRef}/evidenceRefs/${index}/kind`,
            'evidence kind',
          ),
          path: asString(entry['path']) ?? sourceFile,
          ...(asString(entry['description']) ? { description: asString(entry['description']) } : {}),
        };
      })
    : [];
  return refs.length > 0
    ? refs
    : [
        {
          id: sourceId ? `SPEC-EVIDENCE-${sourceId}` : 'SPEC-EVIDENCE-IMPORTED',
          kind: 'source',
          path: sourceFile,
          description: 'Source SPECA-like finding record.',
        },
      ];
}

function gateDecision(raw: unknown, fallbackResult: string, fallbackRationale: string, warnings: ImportWarning[], source: string, pathRef: string): JsonRecord {
  const record = isRecord(raw) ? raw : {};
  const result = normalizeEnum(record['result'] ?? raw, GATE_RESULTS, fallbackResult as (typeof GATE_RESULTS)[number], warnings, source, `${pathRef}/result`, 'gate result');
  return {
    result,
    rationale: asString(record['rationale']) ?? fallbackRationale,
    ...(asStringArray(record['evidenceRefs']).length > 0 ? { evidenceRefs: asStringArray(record['evidenceRefs']) } : {}),
  };
}

function normalizeFalsePositiveRootCause(
  value: unknown,
  result: ReviewResult,
  gates: JsonRecord,
  warnings: ImportWarning[],
  source: string,
  pathRef: string,
): FalsePositiveRootCause | null {
  const rejectedLike = result === 'rejected' || result === 'out-of-scope';
  if (!rejectedLike) {
    if (asString(value)) {
      warning(warnings, 'root-cause-dropped', source, pathRef, `falsePositiveRootCause is only valid for rejected/out-of-scope reviews; emitted null for '${result}'.`);
    }
    return null;
  }
  const candidate = asString(value)?.toLowerCase();
  if (candidate) {
    const normalized = candidate.replace(/[\s_]+/g, '-');
    if ((FALSE_POSITIVE_ROOT_CAUSES as readonly string[]).includes(normalized)) {
      return normalized as FalsePositiveRootCause;
    }
  }
  if (result === 'out-of-scope' || (isRecord(gates['scope']) && gates['scope']['result'] === 'fail')) {
    warning(warnings, 'root-cause-defaulted', source, pathRef, "Missing/unsupported falsePositiveRootCause; defaulted to 'out-of-scope'.");
    return 'out-of-scope';
  }
  warning(warnings, 'root-cause-defaulted', source, pathRef, "Missing/unsupported falsePositiveRootCause; defaulted to 'insufficient-evidence'.");
  return 'insufficient-evidence';
}

function importSummary(
  generatedAt: string,
  inputDir: string,
  outputPaths: SpecaImportOutputPaths,
  artifacts: SecurityArtifactSet,
  warnings: ImportWarning[],
): JsonRecord {
  return {
    schemaVersion: 'security-speca-import-summary/v1',
    generatedAt,
    source: inputDir,
    outputs: outputPaths,
    counts: {
      claims: artifacts.claims.claims.length,
      threats: artifacts.threatModel.threats.length,
      findings: artifacts.findings.findings.length,
      reviews: artifacts.review.reviews.length,
      warnings: warnings.length,
    },
    warnings,
  };
}

function portablePathFrom(baseDir: string, targetPath: string): string {
  return normalizeArtifactPath(targetPath, { repoRoot: baseDir }) ?? targetPath.replace(/\\/g, '/');
}

export function convertSpecaLikeSecurityArtifacts(bundle: SpecaLikeBundle, options: SpecaImportOptions = {}): { artifacts: SecurityArtifactSet; warnings: ImportWarning[] } {
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const warnings = [...bundle.warnings];
  const propertyIdToClaimId = new Map<string, string>();
  const findingIdToCanonicalId = new Map<string, string>();
  const usedClaimIds = new Set<string>();
  const usedFindingIds = new Set<string>();
  const reservedClaimIds = new Set(
    bundle.properties.map((property) => asString(property['id'])).filter((id): id is string => Boolean(id?.startsWith('SEC-CLAIM-'))),
  );
  const reservedFindingIds = new Set(
    bundle.findings.map((finding) => asString(finding['id'])).filter((id): id is string => Boolean(id?.startsWith('SEC-FINDING-'))),
  );

  if (bundle.properties.length === 0) {
    throw new Error('SPECA-like properties input must contain at least one property.');
  }
  if (bundle.threats.length === 0) {
    throw new Error('SPECA-like threats input must contain at least one threat.');
  }
  if (bundle.findings.length === 0) {
    throw new Error('SPECA-like findings input must contain at least one finding.');
  }
  if (bundle.reviews.length === 0) {
    throw new Error('SPECA-like reviews input must contain at least one review.');
  }

  const claims = bundle.properties.map((property, index) => {
    warnUnknownFields(
      warnings,
      bundle.sourceFiles.properties,
      `/properties/${index}`,
      property,
      new Set(['id', 'type', 'statement', 'source', 'sourceUri', 'sourceRefs', 'severity', 'criticality', 'assuranceLevel', 'targetLevel', 'stride', 'cwe', 'threatTags', 'trustBoundary', 'requiredLanes', 'notes']),
    );
    const sourceId = asString(property['id']) ?? formatId('SPECA-PROPERTY', index);
    const claimId = claimIdFor(property, index, usedClaimIds, warnings, bundle.sourceFiles.properties, `/properties/${index}/id`, reservedClaimIds);
    propertyIdToClaimId.set(sourceId, claimId);
    propertyIdToClaimId.set(claimId, claimId);
    const threatTags = isRecord(property['threatTags']) ? property['threatTags'] : {};
    let stride = normalizeStrideArray(property['stride'] ?? threatTags['stride'], warnings, bundle.sourceFiles.properties, `/properties/${index}/stride`);
    let cwe = normalizeCweArray(property['cwe'] ?? threatTags['cwe'], warnings, bundle.sourceFiles.properties, `/properties/${index}/cwe`);
    if (stride.length === 0) {
      warning(warnings, 'missing-stride', bundle.sourceFiles.properties, `/properties/${index}/stride`, "Missing STRIDE tags; defaulted to 'Tampering'.");
      stride = ['Tampering'];
    }
    if (cwe.length === 0) {
      warning(warnings, 'missing-cwe', bundle.sourceFiles.properties, `/properties/${index}/cwe`, "Missing CWE tags; defaulted to 'CWE-20'.");
      cwe = ['CWE-20'];
    }
    return {
      id: claimId,
      type: normalizeEnum(property['type'], CLAIM_TYPES, 'invariant', warnings, bundle.sourceFiles.properties, `/properties/${index}/type`, 'claim type'),
      statement: asString(property['statement']) ?? `Imported SPECA-like property ${sourceId}`,
      sourceRefs: sourceRefFor(property, warnings, bundle.sourceFiles.properties, `/properties/${index}`),
      criticality: normalizeFindingSeverity(property['criticality'] ?? property['severity'], warnings, bundle.sourceFiles.properties, `/properties/${index}/criticality`),
      targetLevel: normalizeAssuranceLevel(property['targetLevel'] ?? property['assuranceLevel'], warnings, bundle.sourceFiles.properties, `/properties/${index}/targetLevel`),
      threatTags: { stride, cwe },
      trustBoundary: trustBoundaryFor(property, warnings, bundle.sourceFiles.properties, `/properties/${index}`),
      requiredLanes: requiredLanesFor(property['requiredLanes'], warnings, bundle.sourceFiles.properties, `/properties/${index}/requiredLanes`),
      provenance: {
        origin: 'imported',
        generator: GENERATOR,
        source: bundle.sourceFiles.properties,
        ...(asString(property['schemaVersion']) ? { version: asString(property['schemaVersion']) } : {}),
      },
      notes: unique([`Imported from SPECA-like property '${sourceId}'.`, ...asStringArray(property['notes'])]),
    };
  });

  const byCriticality = countCriticality();
  for (const claim of claims) {
    byCriticality[claim.criticality as Criticality] += 1;
  }

  const threats = bundle.threats.map((threat, index) => {
    warnUnknownFields(
      warnings,
      bundle.sourceFiles.threats,
      `/threats/${index}`,
      threat,
      new Set(['id', 'propertyId', 'claimId', 'relatedPropertyIds', 'relatedClaimIds', 'stride', 'cwe', 'description', 'trustBoundaryIds', 'notes']),
    );
    const sourceId = asString(threat['id']) ?? formatId('SPECA-THREAT', index);
    const stride = normalizeStride(threat['stride'], warnings, bundle.sourceFiles.threats, `/threats/${index}/stride`) ?? 'Tampering';
    const cwe = normalizeCwe(threat['cwe'], warnings, bundle.sourceFiles.threats, `/threats/${index}/cwe`) ?? 'CWE-20';
    const relatedClaimIds = relatedClaimIdsFor(threat, propertyIdToClaimId, warnings, bundle.sourceFiles.threats, `/threats/${index}`);
    return {
      id: sourceId.startsWith('THREAT-') ? sourceId : formatId('THREAT', index),
      stride,
      cwe,
      description: asString(threat['description']) ?? `Imported SPECA-like threat ${sourceId}.`,
      relatedClaimIds,
      ...(asStringArray(threat['trustBoundaryIds']).length > 0 ? { trustBoundaryIds: asStringArray(threat['trustBoundaryIds']) } : {}),
      notes: unique([`Imported from SPECA-like threat '${sourceId}'.`, ...asStringArray(threat['notes'])]),
    };
  });

  const findings = bundle.findings.map((finding, index) => {
    warnUnknownFields(
      warnings,
      bundle.sourceFiles.findings,
      `/findings/${index}`,
      finding,
      new Set(['id', 'propertyId', 'claimId', 'status', 'severity', 'confidence', 'title', 'summary', 'affectedLocations', 'locations', 'location', 'proofAttempt', 'map', 'prove', 'stressTest', 'counterexample', 'report', 'scopeRefs', 'evidenceRefs', 'notes']),
    );
    const sourceId = asString(finding['id']) ?? formatId('SPECA-FINDING', index);
    const claimRef = asString(finding['claimId']) ?? asString(finding['propertyId']);
    const claimId = (claimRef ? propertyIdToClaimId.get(claimRef) ?? claimRef : undefined) ?? claims[0]?.id ?? 'SEC-CLAIM-001';
    const findingId = findingIdFor(finding, index, usedFindingIds, warnings, bundle.sourceFiles.findings, `/findings/${index}/id`, reservedFindingIds);
    findingIdToCanonicalId.set(sourceId, findingId);
    findingIdToCanonicalId.set(findingId, findingId);
    const severity = normalizeFindingSeverity(finding['severity'], warnings, bundle.sourceFiles.findings, `/findings/${index}/severity`);
    return {
      id: findingId,
      claimId,
      status: normalizeStatus(finding['status'], warnings, bundle.sourceFiles.findings, `/findings/${index}/status`),
      severity,
      confidence: normalizeConfidence(finding['confidence'], warnings, bundle.sourceFiles.findings, `/findings/${index}/confidence`),
      title: asString(finding['title']) ?? `Imported SPECA-like finding ${sourceId}`,
      summary: asString(finding['summary']) ?? 'Imported SPECA-like audit gap.',
      affectedLocations: affectedLocationsFor(finding, warnings, bundle.sourceFiles.findings, `/findings/${index}`),
      proofAttempt: proofAttemptFor(finding, claimId),
      scopeRefs: asStringArray(finding['scopeRefs']).length > 0 ? asStringArray(finding['scopeRefs']) : ['imported-scope'],
      evidenceRefs: evidenceRefsFor(finding, bundle.sourceFiles.findings, sourceId, warnings, `/findings/${index}`),
      provenance: {
        origin: 'imported',
        generator: GENERATOR,
        source: bundle.sourceFiles.findings,
      },
      notes: unique([`Imported from SPECA-like finding '${sourceId}'.`, ...asStringArray(finding['notes'])]),
    };
  });

  const byFindingStatus = countFindingStatus();
  const bySeverity = countCriticality();
  for (const finding of findings) {
    byFindingStatus[statusSummaryKey(finding.status as string)] += 1;
    bySeverity[finding.severity as Criticality] += 1;
  }

  const reviews = bundle.reviews.map((review, index) => {
    warnUnknownFields(
      warnings,
      bundle.sourceFiles.reviews,
      `/reviews/${index}`,
      review,
      new Set(['findingId', 'result', 'gates', 'deadCode', 'trustBoundary', 'scope', 'falsePositiveRootCause', 'reviewerNotes', 'reviewedAt', 'reviewer']),
    );
    const rawGates = isRecord(review['gates']) ? review['gates'] : {};
    const gates = {
      deadCode: gateDecision(rawGates['deadCode'] ?? review['deadCode'], 'unknown', 'SPECA-like import did not provide a dead-code gate rationale.', warnings, bundle.sourceFiles.reviews, `/reviews/${index}/gates/deadCode`),
      trustBoundary: gateDecision(rawGates['trustBoundary'] ?? review['trustBoundary'], 'unknown', 'SPECA-like import did not provide a trust-boundary gate rationale.', warnings, bundle.sourceFiles.reviews, `/reviews/${index}/gates/trustBoundary`),
      scope: gateDecision(rawGates['scope'] ?? review['scope'], 'unknown', 'SPECA-like import did not provide a scope gate rationale.', warnings, bundle.sourceFiles.reviews, `/reviews/${index}/gates/scope`),
    };
    const result = normalizeReviewResult(review['result'], warnings, bundle.sourceFiles.reviews, `/reviews/${index}/result`);
    const rawFindingId = asString(review['findingId']);
    const findingId = (rawFindingId ? findingIdToCanonicalId.get(rawFindingId) : undefined) ?? findings[index]?.id ?? findings[0]?.id ?? 'SEC-FINDING-001';
    if (rawFindingId && !findingIdToCanonicalId.has(rawFindingId)) {
      warning(warnings, 'unknown-finding-ref', bundle.sourceFiles.reviews, `/reviews/${index}/findingId`, `Review referenced unknown finding '${rawFindingId}'; defaulted to '${findingId}'.`);
    }
    return {
      findingId,
      result,
      gates,
      falsePositiveRootCause: normalizeFalsePositiveRootCause(review['falsePositiveRootCause'], result, gates, warnings, bundle.sourceFiles.reviews, `/reviews/${index}/falsePositiveRootCause`),
      reviewerNotes: asStringArray(review['reviewerNotes']),
      ...(asString(review['reviewedAt']) ? { reviewedAt: asString(review['reviewedAt']) } : { reviewedAt: generatedAt }),
      ...(asString(review['reviewer']) ? { reviewer: asString(review['reviewer']) } : { reviewer: GENERATOR }),
    };
  });

  const byReviewResult = countReviewResult();
  const falsePositiveRootCauses = countRootCause();
  for (const review of reviews) {
    byReviewResult[reviewSummaryKey(review.result as string)] += 1;
    const rootCause = review.falsePositiveRootCause;
    if (typeof rootCause === 'string') {
      falsePositiveRootCauses[rootCauseSummaryKey(rootCause)] += 1;
    }
  }

  return {
    warnings,
    artifacts: {
      claims: {
        schemaVersion: 'security-claim/v1',
        generatedAt,
        claims,
        summary: { totalClaims: claims.length, byCriticality },
      },
      threatModel: {
        schemaVersion: 'security-threat-model/v1',
        generatedAt,
        frameworks: ['STRIDE', 'CWE_TOP_25'],
        threats,
        summary: { totalThreats: threats.length },
      },
      findings: {
        schemaVersion: 'security-finding/v1',
        generatedAt,
        findings,
        summary: { totalFindings: findings.length, byStatus: byFindingStatus, bySeverity },
      },
      review: {
        schemaVersion: 'security-review/v1',
        generatedAt,
        reviews,
        summary: { totalReviews: reviews.length, byResult: byReviewResult, falsePositiveRootCauses },
      },
    },
  };
}

async function readJson(filePath: string): Promise<JsonRecord> {
  let parsed: unknown;
  try {
    const content = await fs.readFile(filePath, 'utf8');
    parsed = JSON.parse(content) as unknown;
  } catch (error: unknown) {
    if (typeof error === 'object' && error !== null && 'code' in error && (error as { code?: unknown }).code === 'ENOENT') {
      throw new Error(`Input file not found: ${filePath}`);
    }
    if (error instanceof SyntaxError) {
      throw new Error(`Malformed JSON input: ${filePath}`);
    }
    throw error;
  }
  if (!isRecord(parsed)) {
    throw new Error(`JSON root must be an object: ${filePath}`);
  }
  return parsed;
}

async function findSpecaLikeFile(inputDir: string, prefixes: string[]): Promise<string> {
  const entries = await fs.readdir(inputDir);
  const candidates = entries
    .filter((entry) => entry.endsWith('.json') && prefixes.some((prefix) => entry.startsWith(prefix)))
    .sort();
  if (candidates.length === 0) {
    throw new Error(`No SPECA-like JSON file found in ${inputDir} for prefixes ${prefixes.join(', ')}.`);
  }
  return path.join(inputDir, candidates[0] ?? '');
}

function relOrBase(inputDir: string, filePath: string): string {
  const rel = path.relative(inputDir, filePath);
  return rel && !rel.startsWith('..') ? rel : path.basename(filePath);
}

async function loadSpecaLikeBundle(inputDir: string): Promise<SpecaLikeBundle> {
  const resolvedInputDir = path.resolve(inputDir);
  const files = {
    properties: await findSpecaLikeFile(resolvedInputDir, ['01e']),
    threats: await findSpecaLikeFile(resolvedInputDir, ['02c']),
    findings: await findSpecaLikeFile(resolvedInputDir, ['03']),
    reviews: await findSpecaLikeFile(resolvedInputDir, ['04']),
  };

  const [propertiesDocument, threatsDocument, findingsDocument, reviewsDocument] = await Promise.all([
    readJson(files.properties),
    readJson(files.threats),
    readJson(files.findings),
    readJson(files.reviews),
  ]);

  const warnings: ImportWarning[] = [];
  warnUnknownFields(warnings, relOrBase(resolvedInputDir, files.properties), '', propertiesDocument, new Set(['schemaVersion', 'properties', 'metadata']));
  warnUnknownFields(warnings, relOrBase(resolvedInputDir, files.threats), '', threatsDocument, new Set(['schemaVersion', 'frameworks', 'threats', 'metadata']));
  warnUnknownFields(warnings, relOrBase(resolvedInputDir, files.findings), '', findingsDocument, new Set(['schemaVersion', 'findings', 'metadata']));
  warnUnknownFields(warnings, relOrBase(resolvedInputDir, files.reviews), '', reviewsDocument, new Set(['schemaVersion', 'reviews', 'metadata']));

  return {
    properties: Array.isArray(propertiesDocument['properties']) ? propertiesDocument['properties'].filter(isRecord) : [],
    threats: Array.isArray(threatsDocument['threats']) ? threatsDocument['threats'].filter(isRecord) : [],
    findings: Array.isArray(findingsDocument['findings']) ? findingsDocument['findings'].filter(isRecord) : [],
    reviews: Array.isArray(reviewsDocument['reviews']) ? reviewsDocument['reviews'].filter(isRecord) : [],
    sourceFiles: {
      properties: relOrBase(resolvedInputDir, files.properties),
      threats: relOrBase(resolvedInputDir, files.threats),
      findings: relOrBase(resolvedInputDir, files.findings),
      reviews: relOrBase(resolvedInputDir, files.reviews),
    },
    warnings,
  };
}

async function validateArtifact(repoRoot: string, schemaPath: string, label: string, artifact: unknown): Promise<void> {
  const schema = await readJson(path.join(repoRoot, schemaPath));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  if (!validate(artifact)) {
    throw new Error(`${label} failed schema validation: ${JSON.stringify(validate.errors)}`);
  }
}

async function validateArtifacts(repoRoot: string, artifacts: SecurityArtifactSet): Promise<void> {
  await Promise.all([
    validateArtifact(repoRoot, 'schema/security-claim-v1.schema.json', 'security-claims.json', artifacts.claims),
    validateArtifact(repoRoot, 'schema/security-threat-model-v1.schema.json', 'security-threat-model.json', artifacts.threatModel),
    validateArtifact(repoRoot, 'schema/security-finding-v1.schema.json', 'security-findings.json', artifacts.findings),
    validateArtifact(repoRoot, 'schema/security-review-v1.schema.json', 'security-review.json', artifacts.review),
  ]);
}

function candidateSchemaRoots(preferredRoot?: string): string[] {
  const roots = [preferredRoot, process.cwd()].filter((entry): entry is string => Boolean(entry));
  for (let current = MODULE_DIR; ; current = path.dirname(current)) {
    roots.push(current);
    const parent = path.dirname(current);
    if (parent === current) {
      break;
    }
  }
  return unique(roots.map((entry) => path.resolve(entry)));
}

function resolveSchemaRoot(preferredRoot?: string): string {
  for (const candidate of candidateSchemaRoots(preferredRoot)) {
    if (existsSync(path.join(candidate, 'schema/security-claim-v1.schema.json'))) {
      return candidate;
    }
  }
  throw new Error('Unable to locate ae-framework schema directory for security assurance validation.');
}

function renderImportSummaryMarkdown(summary: JsonRecord): string {
  const counts = isRecord(summary['counts']) ? summary['counts'] : {};
  const warnings = Array.isArray(summary['warnings']) ? summary['warnings'].filter(isRecord) : [];
  const scalar = (value: unknown, fallback = ''): string => {
    if (typeof value === 'string' || typeof value === 'number' || typeof value === 'boolean') {
      return String(value);
    }
    return fallback;
  };
  const count = (key: string, fallback = 0): string => {
    const value = counts[key];
    return typeof value === 'number' && Number.isFinite(value) ? String(value) : String(fallback);
  };
  const lines = [
    '# SPECA-compatible security import summary',
    '',
    `- Generated at: ${scalar(summary['generatedAt'], 'unknown')}`,
    `- Source: ${scalar(summary['source'], 'unknown')}`,
    `- Claims: ${count('claims')}`,
    `- Threats: ${count('threats')}`,
    `- Findings: ${count('findings')}`,
    `- Reviews: ${count('reviews')}`,
    `- Warnings: ${count('warnings', warnings.length)}`,
    '',
    '## Outputs',
    '',
  ];
  const outputs = isRecord(summary['outputs']) ? summary['outputs'] : {};
  for (const [key, value] of Object.entries(outputs)) {
    lines.push(`- ${key}: \`${scalar(value, 'unknown')}\``);
  }
  lines.push('', '## Warnings', '');
  if (warnings.length === 0) {
    lines.push('- None');
  } else {
    for (const entry of warnings) {
      lines.push(
        `- \`${scalar(entry['code'], 'unknown-code')}\` ${scalar(entry['source'], 'unknown-source')}${scalar(entry['path'])}: ${scalar(entry['message'])}`,
      );
    }
  }
  lines.push('');
  return lines.join('\n');
}

async function writeJson(filePath: string, value: unknown): Promise<void> {
  await fs.writeFile(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

export async function importSpecaLikeSecurityArtifacts(inputDir: string, outDir: string, options: SpecaImportOptions = {}): Promise<SpecaImportResult> {
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const resolvedInputDir = path.resolve(inputDir);
  const resolvedOutDir = path.resolve(outDir);
  const repoRoot = resolveSchemaRoot(options.repoRoot);
  const bundle = await loadSpecaLikeBundle(resolvedInputDir);
  const { artifacts, warnings } = convertSpecaLikeSecurityArtifacts(bundle, { ...options, generatedAt });
  if (options.validate !== false) {
    await validateArtifacts(repoRoot, artifacts);
  }

  await fs.mkdir(resolvedOutDir, { recursive: true });
  const outputPaths: SpecaImportOutputPaths = {
    claims: path.join(resolvedOutDir, 'security-claims.json'),
    threatModel: path.join(resolvedOutDir, 'security-threat-model.json'),
    findings: path.join(resolvedOutDir, 'security-findings.json'),
    review: path.join(resolvedOutDir, 'security-review.json'),
    summaryJson: path.join(resolvedOutDir, 'import-summary.json'),
    summaryMarkdown: path.join(resolvedOutDir, 'import-summary.md'),
  };
  const summaryOutputPaths: SpecaImportOutputPaths = {
    claims: portablePathFrom(repoRoot, outputPaths.claims),
    threatModel: portablePathFrom(repoRoot, outputPaths.threatModel),
    findings: portablePathFrom(repoRoot, outputPaths.findings),
    review: portablePathFrom(repoRoot, outputPaths.review),
    summaryJson: portablePathFrom(repoRoot, outputPaths.summaryJson),
    summaryMarkdown: portablePathFrom(repoRoot, outputPaths.summaryMarkdown),
  };
  const summary = importSummary(
    generatedAt,
    portablePathFrom(repoRoot, resolvedInputDir),
    summaryOutputPaths,
    artifacts,
    warnings,
  );

  await Promise.all([
    writeJson(outputPaths.claims, artifacts.claims),
    writeJson(outputPaths.threatModel, artifacts.threatModel),
    writeJson(outputPaths.findings, artifacts.findings),
    writeJson(outputPaths.review, artifacts.review),
    writeJson(outputPaths.summaryJson, summary),
    fs.writeFile(outputPaths.summaryMarkdown, renderImportSummaryMarkdown(summary), 'utf8'),
  ]);

  return { generatedAt, artifacts, warnings, outputPaths };
}
