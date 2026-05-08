import { existsSync, promises as fs } from 'node:fs';
import { createRequire } from 'node:module';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { normalizeArtifactPath as normalizeSharedArtifactPath } from '../../utils/path-normalization.js';

const require = createRequire(import.meta.url);
const Ajv2020 = require('ajv/dist/2020.js') as new (options?: JsonRecord) => {
  compile: (schema: unknown) => ((data: unknown) => boolean) & { errors?: unknown };
};
const addFormats = require('ajv-formats') as (ajv: unknown) => void;
const globRequire = createRequire(require.resolve('glob/package.json'));
const minimatch = (globRequire('minimatch') as {
  minimatch: (pathRef: string, pattern: string, options?: { dot?: boolean; windowsPathsNoEscape?: boolean }) => boolean;
}).minimatch;

type JsonRecord = Record<string, unknown>;
type Severity = 'low' | 'medium' | 'high' | 'critical';
type FindingStatus = 'candidate' | 'needs-human-review' | 'confirmed' | 'rejected' | 'waived' | 'out-of-scope';
type ReviewResult = 'needs-human-review' | 'confirmed' | 'rejected' | 'waived' | 'out-of-scope';
type GateResult = 'pass' | 'fail' | 'unknown' | 'not-applicable';
type SecurityClaimType = 'invariant' | 'precondition' | 'postcondition' | 'assumption';
type AssumptionHandlingMode = 'assumption-validation-required' | 'residual-risk';
type FalsePositiveRootCause =
  | 'dead-code'
  | 'trust-boundary-misunderstanding'
  | 'out-of-scope'
  | 'code-reading-error'
  | 'spec-misinterpretation'
  | 'insufficient-evidence';

type AffectedLocation = {
  path: string;
  startLine: number;
  endLine: number;
  symbol?: string;
  description?: string;
};

type SecurityFinding = {
  id: string;
  claimId: string;
  status: FindingStatus;
  severity: Severity;
  title: string;
  summary: string;
  affectedLocations: AffectedLocation[];
  proofAttempt?: JsonRecord;
  scopeRefs: string[];
  notes: string[];
};

type SecurityFindingDocument = {
  schemaVersion: 'security-finding/v1';
  generatedAt?: string;
  findings: SecurityFinding[];
};

type TrustBoundary = {
  id: string;
  name: string;
  entryPoints: string[];
  attackerControlled: boolean;
  scopeRefs: string[];
};

type SecurityAuditScopeDocument = {
  schemaVersion: 'security-audit-scope/v1';
  inScope: string[];
  outOfScope: string[];
  trustBoundaries: TrustBoundary[];
};

type CodeMapCandidateLocation = {
  path: string;
  startLine: number;
  endLine: number;
  symbol?: string;
};

type CodeMapMapping = {
  claimId: string;
  candidateLocations: CodeMapCandidateLocation[];
};

type SecurityCodeMapDocument = {
  schemaVersion: 'security-code-map/v1';
  mappings: CodeMapMapping[];
};

type SecurityClaim = {
  id: string;
  type: SecurityClaimType;
  statement?: string;
};

type SecurityClaimDocument = {
  schemaVersion: 'security-claim/v1';
  generatedAt?: string;
  claims: SecurityClaim[];
};

type EntrypointReach = {
  path: string;
  startLine?: number;
  endLine?: number;
  symbol?: string;
  reason?: string;
};

type SecurityEntrypoint = {
  id: string;
  kind: string;
  name: string;
  path: string;
  startLine: number;
  endLine: number;
  trustBoundaryIds: string[];
  attackerControlled: boolean;
  reaches: EntrypointReach[];
};

type SecurityEntrypointMapDocument = {
  schemaVersion: 'security-entrypoint-map/v1';
  generatedAt?: string;
  entrypoints: SecurityEntrypoint[];
};

export interface ReviewWarning {
  code: string;
  source?: string;
  path: string;
  message: string;
}

export interface GateDecision {
  result: GateResult;
  rationale: string;
  evidenceRefs?: string[];
}

export interface AssumptionHandling {
  mode: AssumptionHandlingMode;
  rationale: string;
  evidenceRefs?: string[];
}

export interface SecurityReviewEntry {
  findingId: string;
  claimId?: string;
  claimType?: SecurityClaimType;
  severity?: Severity;
  result: ReviewResult;
  gates: {
    deadCode: GateDecision;
    trustBoundary: GateDecision;
    scope: GateDecision;
  };
  falsePositiveRootCause: FalsePositiveRootCause | null;
  assumptionHandling?: AssumptionHandling;
  reviewerNotes: string[];
  reviewedAt?: string;
  reviewer?: string;
}

export interface SecurityReviewDocument {
  schemaVersion: 'security-review/v1';
  generatedAt: string;
  reviews: SecurityReviewEntry[];
  summary: {
    totalReviews: number;
    byResult: Record<'needsHumanReview' | 'confirmed' | 'rejected' | 'waived' | 'outOfScope', number>;
    falsePositiveRootCauses: Record<
      'deadCode' | 'trustBoundaryMisunderstanding' | 'outOfScope' | 'codeReadingError' | 'specMisinterpretation' | 'insufficientEvidence',
      number
    >;
  };
}

export interface SecurityReviewOptions {
  generatedAt?: string;
  repoRoot?: string;
  validate?: boolean;
  entrypointMapPath?: string;
  claimsPath?: string;
}

export interface SecurityReviewOutputPaths {
  review: string;
  summaryMarkdown: string;
}

export interface SecurityReviewResult {
  generatedAt: string;
  review: SecurityReviewDocument;
  warnings: ReviewWarning[];
  outputPaths: SecurityReviewOutputPaths;
}

type ScopeDecisionDetails = {
  decision: GateDecision;
  matchedInScope: string[];
  matchedOutOfScope: string[];
  outsideInScopePaths: string[];
};

type DeadCodeDetails = {
  decision: GateDecision;
  hasMatchedCodeMapLocation: boolean;
};

const GENERATOR = 'security-three-gate-review';
const MODULE_DIR = path.dirname(fileURLToPath(import.meta.url));
const SEVERITIES: readonly Severity[] = ['low', 'medium', 'high', 'critical'];
const FINDING_STATUSES: readonly FindingStatus[] = ['candidate', 'needs-human-review', 'confirmed', 'rejected', 'waived', 'out-of-scope'];
const SECURITY_CLAIM_TYPES: readonly SecurityClaimType[] = ['invariant', 'precondition', 'postcondition', 'assumption'];
const DEAD_CODE_PATH_MARKERS = new Set(['__fixtures__', '__mocks__', 'fixture', 'fixtures', 'mock', 'mocks', 'generated', 'dead', 'unused', 'unreachable', 'orphan']);

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
  return [...new Set(values.filter((entry) => entry.trim().length > 0))];
}

function normalizeArtifactPath(pathRef: string, repoRoot?: string): string {
  const options = repoRoot === undefined ? {} : { repoRoot };
  return normalizeSharedArtifactPath(pathRef, options) ?? pathRef.replace(/\\/g, '/');
}

function normalizeSeverity(value: unknown): Severity {
  const candidate = asString(value)?.toLowerCase();
  if (candidate && (SEVERITIES as readonly string[]).includes(candidate)) {
    return candidate as Severity;
  }
  return 'medium';
}

function normalizeFindingStatus(value: unknown): FindingStatus {
  const candidate = asString(value)?.toLowerCase();
  if (candidate && (FINDING_STATUSES as readonly string[]).includes(candidate)) {
    return candidate as FindingStatus;
  }
  return 'candidate';
}

function normalizeSecurityClaimType(value: unknown): SecurityClaimType | undefined {
  const candidate = asString(value)?.toLowerCase();
  if (candidate && (SECURITY_CLAIM_TYPES as readonly string[]).includes(candidate)) {
    return candidate as SecurityClaimType;
  }
  return undefined;
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
  return [...new Set(roots.map((entry) => path.resolve(entry)))];
}

function resolveSchemaRoot(preferredRoot?: string): string {
  for (const candidate of candidateSchemaRoots(preferredRoot)) {
    if (existsSync(path.join(candidate, 'schema/security-review-v1.schema.json'))) {
      return candidate;
    }
  }
  throw new Error('Unable to locate ae-framework schema directory for security review validation.');
}

function outputPathsFor(outPath: string): SecurityReviewOutputPaths {
  const resolvedOut = path.resolve(outPath);
  if (path.extname(resolvedOut).toLowerCase() === '.json') {
    return {
      review: resolvedOut,
      summaryMarkdown: resolvedOut.replace(/\.json$/i, '.md'),
    };
  }
  return {
    review: path.join(resolvedOut, 'security-review.json'),
    summaryMarkdown: path.join(resolvedOut, 'security-review.md'),
  };
}

async function loadJson(filePath: string): Promise<unknown> {
  try {
    return JSON.parse(await fs.readFile(filePath, 'utf8')) as unknown;
  } catch (error: unknown) {
    if (typeof error === 'object' && error !== null && 'code' in error && (error as { code?: unknown }).code === 'ENOENT') {
      const detail = error instanceof Error ? `: ${error.message}` : '';
      throw new Error(`Input file not found: ${filePath}${detail}`, { cause: error });
    }
    if (error instanceof SyntaxError) {
      throw new Error(`Malformed JSON input: ${filePath}: ${error.message}`, { cause: error });
    }
    throw error;
  }
}

async function validateWithSchema(repoRoot: string, schemaName: string, document: unknown, label: string): Promise<void> {
  const schema = JSON.parse(await fs.readFile(path.join(repoRoot, 'schema', schemaName), 'utf8')) as unknown;
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  if (!validate(document)) {
    throw new Error(`${label} failed schema validation: ${JSON.stringify(validate.errors, null, 2)}`);
  }
}

function parseAffectedLocation(rawLocation: unknown, pathRef: string, repoRoot?: string): AffectedLocation {
  if (!isRecord(rawLocation)) {
    throw new Error(`Affected location ${pathRef} must be an object.`);
  }
  const locationPath = asString(rawLocation['path']);
  if (!locationPath) {
    throw new Error(`Affected location ${pathRef} must have a non-empty path.`);
  }
  const startLine = typeof rawLocation['startLine'] === 'number' ? Math.max(1, Math.floor(rawLocation['startLine'])) : 1;
  const rawEndLine = typeof rawLocation['endLine'] === 'number' ? Math.max(1, Math.floor(rawLocation['endLine'])) : startLine;
  const endLine = Math.max(startLine, rawEndLine);
  const parsed: AffectedLocation = { path: normalizeArtifactPath(locationPath, repoRoot), startLine, endLine };
  const symbol = asString(rawLocation['symbol']);
  if (symbol !== undefined) {
    parsed.symbol = symbol;
  }
  const description = asString(rawLocation['description']);
  if (description !== undefined) {
    parsed.description = description;
  }
  return parsed;
}

function parseFindingDocument(document: unknown, repoRoot?: string): SecurityFindingDocument {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-finding/v1' || !Array.isArray(document['findings'])) {
    throw new Error('Expected security-finding/v1 document with a findings array.');
  }
  const findings = document['findings'].map((rawFinding, findingIndex) => {
    if (!isRecord(rawFinding)) {
      throw new Error(`Security finding at index ${findingIndex} must be an object.`);
    }
    const id = asString(rawFinding['id']);
    const claimId = asString(rawFinding['claimId']);
    const title = asString(rawFinding['title']) ?? `Security finding ${findingIndex + 1}`;
    const summary = asString(rawFinding['summary']) ?? 'No finding summary was provided.';
    if (!id || !claimId) {
      throw new Error(`Security finding at index ${findingIndex} must have non-empty id and claimId.`);
    }
    const affectedLocations = Array.isArray(rawFinding['affectedLocations'])
      ? rawFinding['affectedLocations'].map((rawLocation, locationIndex) => parseAffectedLocation(rawLocation, `/findings/${findingIndex}/affectedLocations/${locationIndex}`, repoRoot))
      : [];
    if (affectedLocations.length === 0) {
      throw new Error(`Security finding ${id} must have at least one affected location.`);
    }
    return {
      id,
      claimId,
      status: normalizeFindingStatus(rawFinding['status']),
      severity: normalizeSeverity(rawFinding['severity']),
      title,
      summary,
      affectedLocations,
      ...(isRecord(rawFinding['proofAttempt']) ? { proofAttempt: rawFinding['proofAttempt'] } : {}),
      scopeRefs: unique(asStringArray(rawFinding['scopeRefs'])),
      notes: unique(asStringArray(rawFinding['notes'])),
    } satisfies SecurityFinding;
  });
  const parsed: SecurityFindingDocument = { schemaVersion: 'security-finding/v1', findings };
  const generatedAt = asString(document['generatedAt']);
  if (generatedAt !== undefined) {
    parsed.generatedAt = generatedAt;
  }
  return parsed;
}

function parseTrustBoundary(rawBoundary: unknown, pathRef: string): TrustBoundary {
  if (!isRecord(rawBoundary)) {
    throw new Error(`Trust boundary ${pathRef} must be an object.`);
  }
  const id = asString(rawBoundary['id']);
  const name = asString(rawBoundary['name']);
  if (!id || !name) {
    throw new Error(`Trust boundary ${pathRef} must have non-empty id and name.`);
  }
  return {
    id,
    name,
    entryPoints: unique(asStringArray(rawBoundary['entryPoints'])),
    attackerControlled: rawBoundary['attackerControlled'] === true,
    scopeRefs: unique(asStringArray(rawBoundary['scopeRefs'])),
  };
}

function parseScopeDocument(document: unknown, repoRoot?: string): SecurityAuditScopeDocument {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-audit-scope/v1') {
    throw new Error('Expected security-audit-scope/v1 document.');
  }
  const inScope = unique(asStringArray(document['inScope']).map((entry) => normalizeArtifactPath(entry, repoRoot)));
  const outOfScope = unique(asStringArray(document['outOfScope']).map((entry) => normalizeArtifactPath(entry, repoRoot)));
  const trustBoundaries = Array.isArray(document['trustBoundaries'])
    ? document['trustBoundaries'].map((rawBoundary, index) => parseTrustBoundary(rawBoundary, `/trustBoundaries/${index}`))
    : [];
  return { schemaVersion: 'security-audit-scope/v1', inScope, outOfScope, trustBoundaries };
}

function parseCodeMapLocation(rawLocation: unknown, pathRef: string, repoRoot?: string): CodeMapCandidateLocation {
  if (!isRecord(rawLocation)) {
    throw new Error(`Code-map candidate location ${pathRef} must be an object.`);
  }
  const locationPath = asString(rawLocation['path']);
  if (!locationPath) {
    throw new Error(`Code-map candidate location ${pathRef} must have a non-empty path.`);
  }
  const startLine = typeof rawLocation['startLine'] === 'number' ? Math.max(1, Math.floor(rawLocation['startLine'])) : 1;
  const rawEndLine = typeof rawLocation['endLine'] === 'number' ? Math.max(1, Math.floor(rawLocation['endLine'])) : startLine;
  const parsed: CodeMapCandidateLocation = {
    path: normalizeArtifactPath(locationPath, repoRoot),
    startLine,
    endLine: Math.max(startLine, rawEndLine),
  };
  const symbol = asString(rawLocation['symbol']);
  if (symbol !== undefined) {
    parsed.symbol = symbol;
  }
  return parsed;
}

function parseCodeMapDocument(document: unknown, repoRoot?: string): SecurityCodeMapDocument {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-code-map/v1' || !Array.isArray(document['mappings'])) {
    throw new Error('Expected security-code-map/v1 document with a mappings array.');
  }
  const mappings = document['mappings'].map((rawMapping, mappingIndex) => {
    if (!isRecord(rawMapping)) {
      throw new Error(`Security code-map mapping at index ${mappingIndex} must be an object.`);
    }
    const claimId = asString(rawMapping['claimId']);
    if (!claimId) {
      throw new Error(`Security code-map mapping at index ${mappingIndex} must have a non-empty claimId.`);
    }
    const candidateLocations = Array.isArray(rawMapping['candidateLocations'])
      ? rawMapping['candidateLocations'].map((rawLocation, locationIndex) => parseCodeMapLocation(rawLocation, `/mappings/${mappingIndex}/candidateLocations/${locationIndex}`, repoRoot))
      : [];
    return { claimId, candidateLocations } satisfies CodeMapMapping;
  });
  return { schemaVersion: 'security-code-map/v1', mappings };
}

function parseClaimDocument(document: unknown): SecurityClaimDocument {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-claim/v1' || !Array.isArray(document['claims'])) {
    throw new Error('Expected security-claim/v1 document with a claims array.');
  }
  const claims = document['claims'].map((rawClaim, claimIndex) => {
    if (!isRecord(rawClaim)) {
      throw new Error(`Security claim at index ${claimIndex} must be an object.`);
    }
    const id = asString(rawClaim['id']);
    const type = normalizeSecurityClaimType(rawClaim['type']);
    if (!id || !type) {
      throw new Error(`Security claim at index ${claimIndex} must have non-empty id and supported type.`);
    }
    const parsed: SecurityClaim = { id, type };
    const statement = asString(rawClaim['statement']);
    if (statement !== undefined) {
      parsed.statement = statement;
    }
    return parsed;
  });
  const parsed: SecurityClaimDocument = { schemaVersion: 'security-claim/v1', claims };
  const generatedAt = asString(document['generatedAt']);
  if (generatedAt !== undefined) {
    parsed.generatedAt = generatedAt;
  }
  return parsed;
}

function claimMapFromDocument(claims?: SecurityClaimDocument): Map<string, SecurityClaim> | undefined {
  if (!claims) {
    return undefined;
  }
  return new Map(claims.claims.map((claim) => [claim.id, claim]));
}

function parseEntrypointReach(rawReach: unknown, pathRef: string, repoRoot?: string): EntrypointReach {
  if (!isRecord(rawReach)) {
    throw new Error(`Entrypoint reach ${pathRef} must be an object.`);
  }
  const reachPath = asString(rawReach['path']);
  if (!reachPath) {
    throw new Error(`Entrypoint reach ${pathRef} must have a non-empty path.`);
  }
  const parsed: EntrypointReach = {
    path: normalizeArtifactPath(reachPath, repoRoot),
  };
  const hasStartLine = typeof rawReach['startLine'] === 'number';
  const hasEndLine = typeof rawReach['endLine'] === 'number';
  if (hasStartLine !== hasEndLine) {
    throw new Error(`Entrypoint reach ${pathRef} must provide both startLine and endLine when using a line range.`);
  }
  if (hasStartLine && hasEndLine) {
    const startLine = typeof rawReach['startLine'] === 'number' ? Math.max(1, Math.floor(rawReach['startLine'])) : 1;
    const rawEndLine = typeof rawReach['endLine'] === 'number' ? Math.max(1, Math.floor(rawReach['endLine'])) : startLine;
    parsed.startLine = startLine;
    parsed.endLine = Math.max(startLine, rawEndLine);
  }
  const symbol = asString(rawReach['symbol']);
  if (symbol !== undefined) {
    parsed.symbol = symbol;
  }
  const reason = asString(rawReach['reason']);
  if (reason !== undefined) {
    parsed.reason = reason;
  }
  return parsed;
}

function parseEntrypoint(rawEntrypoint: unknown, pathRef: string, repoRoot?: string): SecurityEntrypoint {
  if (!isRecord(rawEntrypoint)) {
    throw new Error(`Security entrypoint ${pathRef} must be an object.`);
  }
  const id = asString(rawEntrypoint['id']);
  const kind = asString(rawEntrypoint['kind']);
  const name = asString(rawEntrypoint['name']);
  const entrypointPath = asString(rawEntrypoint['path']);
  if (!id || !kind || !name || !entrypointPath) {
    throw new Error(`Security entrypoint ${pathRef} must have non-empty id, kind, name, and path.`);
  }
  const startLine = typeof rawEntrypoint['startLine'] === 'number' ? Math.max(1, Math.floor(rawEntrypoint['startLine'])) : 1;
  const rawEndLine = typeof rawEntrypoint['endLine'] === 'number' ? Math.max(1, Math.floor(rawEntrypoint['endLine'])) : startLine;
  const reaches = Array.isArray(rawEntrypoint['reaches'])
    ? rawEntrypoint['reaches'].map((rawReach, reachIndex) => parseEntrypointReach(rawReach, `${pathRef}/reaches/${reachIndex}`, repoRoot))
    : [];
  return {
    id,
    kind,
    name,
    path: normalizeArtifactPath(entrypointPath, repoRoot),
    startLine,
    endLine: Math.max(startLine, rawEndLine),
    trustBoundaryIds: unique(asStringArray(rawEntrypoint['trustBoundaryIds'])),
    attackerControlled: rawEntrypoint['attackerControlled'] === true,
    reaches,
  };
}

function parseEntrypointMapDocument(document: unknown, repoRoot?: string): SecurityEntrypointMapDocument {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-entrypoint-map/v1' || !Array.isArray(document['entrypoints'])) {
    throw new Error('Expected security-entrypoint-map/v1 document with an entrypoints array.');
  }
  const entrypoints = document['entrypoints'].map((rawEntrypoint, entrypointIndex) =>
    parseEntrypoint(rawEntrypoint, `/entrypoints/${entrypointIndex}`, repoRoot),
  );
  const parsed: SecurityEntrypointMapDocument = { schemaVersion: 'security-entrypoint-map/v1', entrypoints };
  const generatedAt = asString(document['generatedAt']);
  if (generatedAt !== undefined) {
    parsed.generatedAt = generatedAt;
  }
  return parsed;
}

function matchingGlobs(pathRef: string, patterns: string[], repoRoot?: string): string[] {
  const normalizedPath = normalizeArtifactPath(pathRef, repoRoot);
  return patterns.filter((pattern) => minimatch(normalizedPath, normalizeArtifactPath(pattern, repoRoot), { dot: true, windowsPathsNoEscape: true }));
}

function decideScope(finding: SecurityFinding, scope: SecurityAuditScopeDocument, repoRoot?: string): ScopeDecisionDetails {
  const matchedOutOfScope = unique(finding.affectedLocations.flatMap((location) => matchingGlobs(location.path, scope.outOfScope, repoRoot)));
  const matchedInScope = unique(finding.affectedLocations.flatMap((location) => matchingGlobs(location.path, scope.inScope, repoRoot)));
  const outsideInScopePaths = finding.affectedLocations
    .map((location) => location.path)
    .filter((locationPath) => matchingGlobs(locationPath, scope.inScope, repoRoot).length === 0);

  if (matchedOutOfScope.length > 0) {
    return {
      matchedInScope,
      matchedOutOfScope,
      outsideInScopePaths,
      decision: {
        result: 'fail',
        rationale: `At least one affected path is excluded by audit scope outOfScope globs: ${matchedOutOfScope.join(', ')}.`,
        evidenceRefs: matchedOutOfScope,
      },
    };
  }

  if (outsideInScopePaths.length > 0) {
    return {
      matchedInScope,
      matchedOutOfScope,
      outsideInScopePaths,
      decision: {
        result: 'fail',
        rationale: `Affected path(s) are not covered by audit scope inScope globs: ${outsideInScopePaths.join(', ')}.`,
        evidenceRefs: outsideInScopePaths,
      },
    };
  }

  return {
    matchedInScope,
    matchedOutOfScope,
    outsideInScopePaths,
    decision: {
      result: 'pass',
      rationale: `All affected paths are covered by audit scope inScope globs (${matchedInScope.join(', ')}).`,
      evidenceRefs: matchedInScope,
    },
  };
}

function locationsOverlap(left: { startLine: number; endLine: number }, right: { startLine: number; endLine: number }): boolean {
  return left.startLine <= right.endLine && right.startLine <= left.endLine;
}

function sameLocationPath(left: string, right: string): boolean {
  return normalizeArtifactPath(left) === normalizeArtifactPath(right);
}

function codeMapLocationMatches(findingLocation: AffectedLocation, candidateLocation: CodeMapCandidateLocation): boolean {
  if (!sameLocationPath(findingLocation.path, candidateLocation.path)) {
    return false;
  }
  if (!locationsOverlap(findingLocation, candidateLocation)) {
    return false;
  }
  if (findingLocation.symbol && candidateLocation.symbol && findingLocation.symbol !== candidateLocation.symbol) {
    return false;
  }
  return true;
}

function looksLikeDeadCodePath(locationPath: string): boolean {
  const parts = normalizeArtifactPath(locationPath)
    .toLowerCase()
    .split(/[/.\\_-]+/)
    .filter(Boolean);
  return parts.some((part) => DEAD_CODE_PATH_MARKERS.has(part));
}

function findingText(finding: SecurityFinding): string {
  const proofAttempt = finding.proofAttempt ?? {};
  return [
    finding.title,
    finding.summary,
    ...finding.notes,
    asString(proofAttempt['map']),
    asString(proofAttempt['prove']),
    asString(proofAttempt['stressTest']),
    asString(proofAttempt['report']),
  ].filter((entry): entry is string => Boolean(entry)).join(' ').toLowerCase();
}

function textSuggestsDeadCode(finding: SecurityFinding): boolean {
  const text = findingText(finding);
  return /\b(dead code|unreachable|unused|test-only|fixture-only|generated-only|not reachable|no production entry point)\b/.test(text);
}

function decideDeadCode(finding: SecurityFinding, codeMapByClaim: Map<string, CodeMapMapping>, scopeDecision: GateDecision): DeadCodeDetails {
  if (finding.status !== 'candidate' && finding.status !== 'needs-human-review') {
    return {
      hasMatchedCodeMapLocation: false,
      decision: {
        result: 'not-applicable',
        rationale: `Finding status is already ${finding.status}; candidate dead-code review was not applied.`,
      },
    };
  }

  if (scopeDecision.result === 'fail') {
    return {
      hasMatchedCodeMapLocation: false,
      decision: {
        result: 'unknown',
        rationale: 'Dead-code reachability was not evaluated because the scope gate failed first.',
      },
    };
  }

  const mapping = codeMapByClaim.get(finding.claimId);
  const candidateLocations = mapping?.candidateLocations ?? [];
  const hasMatchedCodeMapLocation = finding.affectedLocations.some((affectedLocation) =>
    candidateLocations.some((candidateLocation) => codeMapLocationMatches(affectedLocation, candidateLocation)),
  );

  if (hasMatchedCodeMapLocation && !finding.affectedLocations.some((location) => looksLikeDeadCodePath(location.path)) && !textSuggestsDeadCode(finding)) {
    return {
      hasMatchedCodeMapLocation,
      decision: {
        result: 'pass',
        rationale: 'At least one affected location overlaps the security-code-map candidate locations for the same claim.',
        evidenceRefs: finding.affectedLocations.map((location) => `${location.path}:${location.startLine}-${location.endLine}`),
      },
    };
  }

  if (finding.affectedLocations.some((location) => looksLikeDeadCodePath(location.path)) || textSuggestsDeadCode(finding)) {
    return {
      hasMatchedCodeMapLocation,
      decision: {
        result: 'fail',
        rationale: 'Affected location or proof-attempt text suggests test-only, generated-only, unused, or unreachable code.',
        evidenceRefs: finding.affectedLocations.map((location) => location.path),
      },
    };
  }

  if (mapping) {
    return {
      hasMatchedCodeMapLocation,
      decision: {
        result: 'fail',
        rationale: 'Affected location does not overlap any security-code-map candidate location for the same claim; classify as suspected dead/unmapped code for the MVP review.',
        evidenceRefs: candidateLocations.map((location) => `${location.path}:${location.startLine}-${location.endLine}`),
      },
    };
  }

  return {
    hasMatchedCodeMapLocation,
    decision: {
      result: 'unknown',
      rationale: `No security-code-map mapping was available for claim ${finding.claimId}; reachability remains unknown.`,
    },
  };
}

function boundaryKeys(boundary: TrustBoundary): string[] {
  return unique([boundary.id, boundary.name, ...boundary.entryPoints, ...boundary.scopeRefs].map((entry) => entry.toLowerCase()));
}

function referencedBoundaries(finding: SecurityFinding, scope: SecurityAuditScopeDocument): TrustBoundary[] {
  const refs = unique(finding.scopeRefs.map((entry) => entry.toLowerCase()));
  if (refs.length === 0) {
    return [];
  }
  return scope.trustBoundaries.filter((boundary) => boundaryKeys(boundary).some((key) => refs.includes(key)));
}

function locationRef(location: { path: string; startLine: number; endLine: number }): string {
  return `${location.path}:${location.startLine}-${location.endLine}`;
}

function entrypointReachMatchesAffectedLocation(reach: EntrypointReach, affectedLocation: AffectedLocation): boolean {
  if (!sameLocationPath(reach.path, affectedLocation.path)) {
    return false;
  }
  if (reach.startLine !== undefined && reach.endLine !== undefined) {
    const reachRange = { startLine: reach.startLine, endLine: reach.endLine };
    if (!locationsOverlap(reachRange, affectedLocation)) {
      return false;
    }
  }
  if (reach.symbol && affectedLocation.symbol && reach.symbol !== affectedLocation.symbol) {
    return false;
  }
  return true;
}

type EntrypointReachMatch = {
  entrypoint: SecurityEntrypoint;
  reach: EntrypointReach;
  matchedBoundaryIds: string[];
};

function entrypointScopeBoundaryIds(entrypoint: SecurityEntrypoint, scope: SecurityAuditScopeDocument): string[] {
  const scopeBoundaryIds = new Set(scope.trustBoundaries.map((boundary) => boundary.id));
  return entrypoint.trustBoundaryIds.filter((boundaryId) => scopeBoundaryIds.has(boundaryId));
}

function matchingEntrypointReachEvidence(
  finding: SecurityFinding,
  scope: SecurityAuditScopeDocument,
  entrypointMap: SecurityEntrypointMapDocument,
): EntrypointReachMatch[] {
  const matches: EntrypointReachMatch[] = [];
  for (const entrypoint of entrypointMap.entrypoints) {
    const matchedBoundaryIds = entrypointScopeBoundaryIds(entrypoint, scope);
    for (const reach of entrypoint.reaches) {
      if (finding.affectedLocations.some((affectedLocation) => entrypointReachMatchesAffectedLocation(reach, affectedLocation))) {
        matches.push({ entrypoint, reach, matchedBoundaryIds });
      }
    }
  }
  return matches;
}

function evidenceRefsForEntrypointMatches(matches: EntrypointReachMatch[]): string[] {
  return unique(
    matches.flatMap((match) => [
      match.entrypoint.id,
      ...match.matchedBoundaryIds,
      match.reach.startLine !== undefined && match.reach.endLine !== undefined ? locationRef({ path: match.reach.path, startLine: match.reach.startLine, endLine: match.reach.endLine }) : match.reach.path,
    ]),
  );
}

function decideTrustBoundaryFromEntrypoints(
  finding: SecurityFinding,
  scope: SecurityAuditScopeDocument,
  entrypointMap: SecurityEntrypointMapDocument,
): GateDecision {
  const reachMatches = matchingEntrypointReachEvidence(finding, scope, entrypointMap);
  const scopedMatches = reachMatches.filter((match) => match.matchedBoundaryIds.length > 0);

  if (scopedMatches.length === 0) {
    return {
      result: 'unknown',
      rationale: 'No entrypoint-map reachability evidence matched affected locations and audit scope trust boundaries.',
    };
  }

  const attackerControlledMatches = scopedMatches.filter((match) => match.entrypoint.attackerControlled);
  if (attackerControlledMatches.length > 0) {
    return {
      result: 'pass',
      rationale: `Matched attacker-controlled entrypoint evidence: ${unique(attackerControlledMatches.map((match) => match.entrypoint.id)).join(', ')}.`,
      evidenceRefs: evidenceRefsForEntrypointMatches(attackerControlledMatches),
    };
  }

  return {
    result: 'fail',
    rationale: `Matching entrypoint evidence is not attacker-controlled: ${unique(scopedMatches.map((match) => match.entrypoint.id)).join(', ')}.`,
    evidenceRefs: evidenceRefsForEntrypointMatches(scopedMatches),
  };
}

function decideTrustBoundary(
  finding: SecurityFinding,
  scope: SecurityAuditScopeDocument,
  scopeDecision: GateDecision,
  deadCodeDecision: GateDecision,
  entrypointMap?: SecurityEntrypointMapDocument,
): GateDecision {
  if (finding.status !== 'candidate' && finding.status !== 'needs-human-review') {
    return {
      result: 'not-applicable',
      rationale: `Finding status is already ${finding.status}; candidate trust-boundary review was not applied.`,
    };
  }

  if (scopeDecision.result === 'fail') {
    return {
      result: 'unknown',
      rationale: 'Trust-boundary involvement was not evaluated because the scope gate failed first.',
    };
  }

  if (deadCodeDecision.result === 'fail') {
    return {
      result: 'unknown',
      rationale: 'Trust-boundary involvement remains unknown because the dead-code gate failed first.',
    };
  }

  if (entrypointMap) {
    return decideTrustBoundaryFromEntrypoints(finding, scope, entrypointMap);
  }

  const matchedBoundaries = referencedBoundaries(finding, scope);
  if (matchedBoundaries.length === 0) {
    return {
      result: 'unknown',
      rationale: 'No explicit trust boundary reference matched the audit scope; attacker-controlled reachability remains unknown.',
    };
  }

  if (matchedBoundaries.some((boundary) => boundary.attackerControlled)) {
    return {
      result: 'pass',
      rationale: `Matched attacker-controlled trust boundary: ${matchedBoundaries.filter((boundary) => boundary.attackerControlled).map((boundary) => boundary.id).join(', ')}.`,
      evidenceRefs: matchedBoundaries.map((boundary) => boundary.id),
    };
  }

  return {
    result: 'fail',
    rationale: `Matched trust boundary is not marked attacker-controlled: ${matchedBoundaries.map((boundary) => boundary.id).join(', ')}.`,
    evidenceRefs: matchedBoundaries.map((boundary) => boundary.id),
  };
}

function resultForNonCandidateStatus(status: FindingStatus): { result: ReviewResult; rootCause: FalsePositiveRootCause | null } | undefined {
  if (status === 'confirmed') {
    return { result: 'confirmed', rootCause: null };
  }
  if (status === 'waived') {
    return { result: 'waived', rootCause: null };
  }
  if (status === 'out-of-scope') {
    return { result: 'out-of-scope', rootCause: 'out-of-scope' };
  }
  if (status === 'rejected') {
    return { result: 'rejected', rootCause: 'insufficient-evidence' };
  }
  return undefined;
}

function decideReviewResult(finding: SecurityFinding, gates: SecurityReviewEntry['gates']): { result: ReviewResult; rootCause: FalsePositiveRootCause | null } {
  const preReviewed = resultForNonCandidateStatus(finding.status);
  if (preReviewed) {
    return preReviewed;
  }

  if (gates.scope.result === 'fail') {
    return { result: 'out-of-scope', rootCause: 'out-of-scope' };
  }
  if (gates.deadCode.result === 'fail') {
    return { result: 'rejected', rootCause: 'dead-code' };
  }
  if (gates.trustBoundary.result === 'fail') {
    return { result: 'rejected', rootCause: 'trust-boundary-misunderstanding' };
  }
  return { result: 'needs-human-review', rootCause: null };
}

function assumptionHandlingFor(
  finding: SecurityFinding,
  result: ReviewResult,
  rootCause: FalsePositiveRootCause | null,
): AssumptionHandling {
  const validationRequired = result === 'needs-human-review' || result === 'confirmed';
  const mode: AssumptionHandlingMode = validationRequired ? 'assumption-validation-required' : 'residual-risk';
  const rationale = validationRequired
    ? `Finding ${finding.id} is derived from an assumption claim; validate the assumed environment, scope, and trust-boundary evidence before treating it as a vulnerability.`
    : `Finding ${finding.id} is derived from an assumption claim and was classified as ${result}${rootCause ? ` (${rootCause})` : ''}; keep the assumption disposition traceable as residual-risk evidence.`;
  return {
    mode,
    rationale,
    evidenceRefs: unique([finding.claimId, finding.id]),
  };
}

function reviewerNotesFor(
  finding: SecurityFinding,
  gates: SecurityReviewEntry['gates'],
  result: ReviewResult,
  rootCause: FalsePositiveRootCause | null,
  claim?: SecurityClaim,
  assumptionHandling?: AssumptionHandling,
): string[] {
  const notes = [
    `Severity preserved from finding: ${finding.severity}.`,
    'Rule-based MVP review only; exploitability confirmation and full reachability analysis are out of scope.',
  ];
  if (result === 'needs-human-review') {
    notes.push('Candidate finding remains unresolved and requires human security review before confirmation.');
  }
  if (gates.trustBoundary.result === 'unknown') {
    notes.push('Trust boundary involvement is unknown from available scope/code-map evidence.');
  }
  if (rootCause === 'dead-code') {
    notes.push('Classified as a false-positive candidate because the affected path appears dead, generated, or unmapped by the code-map pre-resolution artifact.');
  }
  if (rootCause === 'out-of-scope') {
    notes.push('Classified as out-of-scope based on audit scope glob rules.');
  }
  if (claim) {
    notes.push(`Security claim type: ${claim.type}.`);
  }
  if (claim?.type === 'assumption' && assumptionHandling) {
    notes.push('Assumption-derived finding is handled as assumption validation or residual-risk evidence, not as a direct vulnerability classification.');
    if (assumptionHandling.mode === 'assumption-validation-required') {
      notes.push('Assumption validation is required before this finding can be promoted to a vulnerability or closed as supported evidence.');
    } else {
      notes.push('Assumption-derived finding disposition is retained as residual-risk evidence.');
    }
  }
  return unique(notes);
}

function reviewEntryForFinding(
  finding: SecurityFinding,
  scope: SecurityAuditScopeDocument,
  codeMapByClaim: Map<string, CodeMapMapping>,
  generatedAt: string,
  repoRoot?: string,
  entrypointMap?: SecurityEntrypointMapDocument,
  claim?: SecurityClaim,
): SecurityReviewEntry {
  const scopeDetails = decideScope(finding, scope, repoRoot);
  const deadCodeDetails = decideDeadCode(finding, codeMapByClaim, scopeDetails.decision);
  const trustBoundary = decideTrustBoundary(finding, scope, scopeDetails.decision, deadCodeDetails.decision, entrypointMap);
  const gates = {
    deadCode: deadCodeDetails.decision,
    trustBoundary,
    scope: scopeDetails.decision,
  };
  const decision = decideReviewResult(finding, gates);
  const assumptionHandling = claim?.type === 'assumption'
    ? assumptionHandlingFor(finding, decision.result, decision.rootCause)
    : undefined;
  const entry: SecurityReviewEntry = {
    findingId: finding.id,
    severity: finding.severity,
    result: decision.result,
    gates,
    falsePositiveRootCause: decision.rootCause,
    reviewerNotes: reviewerNotesFor(finding, gates, decision.result, decision.rootCause, claim, assumptionHandling),
    reviewedAt: generatedAt,
    reviewer: GENERATOR,
  };
  if (claim) {
    entry.claimId = finding.claimId;
    entry.claimType = claim.type;
  }
  if (assumptionHandling) {
    entry.assumptionHandling = assumptionHandling;
  }
  return entry;
}

function reviewSummaryKey(result: ReviewResult): keyof SecurityReviewDocument['summary']['byResult'] {
  if (result === 'needs-human-review') {
    return 'needsHumanReview';
  }
  if (result === 'out-of-scope') {
    return 'outOfScope';
  }
  return result;
}

function rootCauseSummaryKey(rootCause: FalsePositiveRootCause): keyof SecurityReviewDocument['summary']['falsePositiveRootCauses'] {
  if (rootCause === 'dead-code') {
    return 'deadCode';
  }
  if (rootCause === 'trust-boundary-misunderstanding') {
    return 'trustBoundaryMisunderstanding';
  }
  if (rootCause === 'out-of-scope') {
    return 'outOfScope';
  }
  if (rootCause === 'code-reading-error') {
    return 'codeReadingError';
  }
  if (rootCause === 'spec-misinterpretation') {
    return 'specMisinterpretation';
  }
  return 'insufficientEvidence';
}

function countReviewResults(): SecurityReviewDocument['summary']['byResult'] {
  return { needsHumanReview: 0, confirmed: 0, rejected: 0, waived: 0, outOfScope: 0 };
}

function countRootCauses(): SecurityReviewDocument['summary']['falsePositiveRootCauses'] {
  return {
    deadCode: 0,
    trustBoundaryMisunderstanding: 0,
    outOfScope: 0,
    codeReadingError: 0,
    specMisinterpretation: 0,
    insufficientEvidence: 0,
  };
}

function summarizeReviews(reviews: SecurityReviewEntry[]): SecurityReviewDocument['summary'] {
  const byResult = countReviewResults();
  const falsePositiveRootCauses = countRootCauses();
  for (const review of reviews) {
    byResult[reviewSummaryKey(review.result)] += 1;
    if (review.falsePositiveRootCause !== null) {
      falsePositiveRootCauses[rootCauseSummaryKey(review.falsePositiveRootCause)] += 1;
    }
  }
  return { totalReviews: reviews.length, byResult, falsePositiveRootCauses };
}

export function buildSecurityThreeGateReview(
  findings: SecurityFindingDocument,
  scope: SecurityAuditScopeDocument,
  codeMap: SecurityCodeMapDocument,
  generatedAt: string,
  repoRoot?: string,
  entrypointMap?: SecurityEntrypointMapDocument,
  claims?: SecurityClaimDocument,
): SecurityReviewDocument {
  const codeMapByClaim = new Map(codeMap.mappings.map((mapping) => [mapping.claimId, mapping]));
  const claimById = claimMapFromDocument(claims);
  const reviews = findings.findings.map((finding) =>
    reviewEntryForFinding(finding, scope, codeMapByClaim, generatedAt, repoRoot, entrypointMap, claimById?.get(finding.claimId)),
  );
  return {
    schemaVersion: 'security-review/v1',
    generatedAt,
    reviews,
    summary: summarizeReviews(reviews),
  };
}

function renderGate(gate: GateDecision): string {
  return `${gate.result} — ${gate.rationale}`;
}

function renderSecurityReviewMarkdown(result: SecurityReviewResult): string {
  const summary = result.review.summary;
  const lines = [
    '# Security three-gate review summary',
    '',
    `- Generated at: ${result.generatedAt}`,
    `- Total reviews: ${summary.totalReviews}`,
    `- Needs human review: ${summary.byResult.needsHumanReview}`,
    `- Confirmed: ${summary.byResult.confirmed}`,
    `- Rejected: ${summary.byResult.rejected}`,
    `- Waived: ${summary.byResult.waived}`,
    `- Out of scope: ${summary.byResult.outOfScope}`,
    `- Dead-code root causes: ${summary.falsePositiveRootCauses.deadCode}`,
    `- Trust-boundary root causes: ${summary.falsePositiveRootCauses.trustBoundaryMisunderstanding}`,
    `- Out-of-scope root causes: ${summary.falsePositiveRootCauses.outOfScope}`,
    `- Warnings: ${result.warnings.length}`,
    '',
    '## Reviews',
    '',
    '| Finding | Claim type | Severity | Result | Assumption handling | Dead Code | Trust Boundary | Scope | Root cause |',
    '| --- | --- | --- | --- | --- | --- | --- | --- | --- |',
  ];
  for (const review of result.review.reviews) {
    lines.push(`| ${review.findingId} | ${review.claimType ?? 'n/a'} | ${review.severity ?? 'unknown'} | ${review.result} | ${review.assumptionHandling?.mode ?? 'n/a'} | ${review.gates.deadCode.result} | ${review.gates.trustBoundary.result} | ${review.gates.scope.result} | ${review.falsePositiveRootCause ?? 'n/a'} |`);
  }
  lines.push('', '## Review detail', '');
  for (const review of result.review.reviews) {
    lines.push(
      `### ${review.findingId}`,
      '',
      `- Claim ID: ${review.claimId ?? 'n/a'}`,
      `- Claim type: ${review.claimType ?? 'n/a'}`,
      `- Severity: ${review.severity ?? 'unknown'}`,
      `- Result: ${review.result}`,
      `- False-positive root cause: ${review.falsePositiveRootCause ?? 'n/a'}`,
      `- Assumption handling: ${review.assumptionHandling ? `${review.assumptionHandling.mode} — ${review.assumptionHandling.rationale}` : 'n/a'}`,
      `- Dead Code: ${renderGate(review.gates.deadCode)}`,
      `- Trust Boundary: ${renderGate(review.gates.trustBoundary)}`,
      `- Scope: ${renderGate(review.gates.scope)}`,
      '- Reviewer notes:',
      ...review.reviewerNotes.map((note) => `  - ${note}`),
      '',
    );
  }
  if (result.warnings.length > 0) {
    lines.push('## Warnings', '');
    for (const entry of result.warnings) {
      lines.push(`- ${entry.code} ${entry.path}: ${entry.message}`);
    }
    lines.push('');
  }
  return `${lines.join('\n').trimEnd()}\n`;
}

async function writeJson(filePath: string, value: unknown): Promise<void> {
  await fs.mkdir(path.dirname(filePath), { recursive: true });
  await fs.writeFile(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

export async function generateSecurityThreeGateReview(
  findingsPath: string,
  scopePath: string,
  codeMapPath: string,
  outPath: string,
  options: SecurityReviewOptions = {},
): Promise<SecurityReviewResult> {
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const shouldValidate = options.validate !== false;
  const schemaRoot = resolveSchemaRoot(options.repoRoot);
  const artifactRepoRoot = options.repoRoot ?? schemaRoot;

  const [findingsDocument, scopeDocument, codeMapDocument, entrypointMapDocument, claimsDocument] = await Promise.all([
    loadJson(findingsPath),
    loadJson(scopePath),
    loadJson(codeMapPath),
    options.entrypointMapPath ? loadJson(options.entrypointMapPath) : Promise.resolve(undefined),
    options.claimsPath ? loadJson(options.claimsPath) : Promise.resolve(undefined),
  ]);

  if (shouldValidate) {
    const validationTasks = [
      validateWithSchema(schemaRoot, 'security-finding-v1.schema.json', findingsDocument, 'security-finding/v1 input'),
      validateWithSchema(schemaRoot, 'security-audit-scope-v1.schema.json', scopeDocument, 'security-audit-scope/v1 input'),
      validateWithSchema(schemaRoot, 'security-code-map-v1.schema.json', codeMapDocument, 'security-code-map/v1 input'),
    ];
    if (entrypointMapDocument !== undefined) {
      validationTasks.push(validateWithSchema(schemaRoot, 'security-entrypoint-map-v1.schema.json', entrypointMapDocument, 'security-entrypoint-map/v1 input'));
    }
    if (claimsDocument !== undefined) {
      validationTasks.push(validateWithSchema(schemaRoot, 'security-claim-v1.schema.json', claimsDocument, 'security-claim/v1 input'));
    }
    await Promise.all(validationTasks);
  }

  const findings = parseFindingDocument(findingsDocument, artifactRepoRoot);
  const scope = parseScopeDocument(scopeDocument, artifactRepoRoot);
  const codeMap = parseCodeMapDocument(codeMapDocument, artifactRepoRoot);
  const entrypointMap = entrypointMapDocument === undefined ? undefined : parseEntrypointMapDocument(entrypointMapDocument, artifactRepoRoot);
  const claims = claimsDocument === undefined ? undefined : parseClaimDocument(claimsDocument);
  const review = buildSecurityThreeGateReview(findings, scope, codeMap, generatedAt, artifactRepoRoot, entrypointMap, claims);
  const warnings: ReviewWarning[] = [];
  const outputPaths = outputPathsFor(outPath);
  const result: SecurityReviewResult = { generatedAt, review, warnings, outputPaths };

  if (shouldValidate) {
    await validateWithSchema(schemaRoot, 'security-review-v1.schema.json', review, 'security-review/v1 output');
  }

  await writeJson(outputPaths.review, review);
  await fs.mkdir(path.dirname(outputPaths.summaryMarkdown), { recursive: true });
  await fs.writeFile(outputPaths.summaryMarkdown, renderSecurityReviewMarkdown(result), 'utf8');

  return result;
}
