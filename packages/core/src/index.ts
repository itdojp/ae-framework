import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { Ajv2020, type ErrorObject, type ValidateFunction } from 'ajv/dist/2020.js';
import yaml from 'yaml';

const require = createRequire(import.meta.url);
const addFormats = require('ajv-formats') as (ajv: Ajv2020) => Ajv2020;

const moduleDir = path.dirname(fileURLToPath(import.meta.url));
const packageRoot = path.resolve(moduleDir, '..');
const schemaRoot = path.join(packageRoot, 'schema');

const LANE_ORDER = ['spec', 'behavior', 'adversarial', 'model', 'proof', 'runtime'] as const;
const CURATED_SCHEMA_FILES = [
  'artifact-metadata.schema.json',
  'envelope.schema.json',
  'producer-normalization-summary.schema.json',
  'assurance-profile.schema.json',
  'assurance-summary.schema.json',
  'claim-evidence-manifest.schema.json',
  'change-package-v2.schema.json',
  'ae-handoff.schema.json',
  'policy-decision-v1.schema.json',
  'policy-gate-summary-v1.schema.json',
  'verify-lite-run-summary.schema.json',
  'release-policy.schema.json',
] as const;

export type Lane = typeof LANE_ORDER[number];
export type SourceKind = 'spec-derived' | 'source-derived' | 'model-derived' | 'runtime-derived' | 'manual' | 'unknown';
export type ClaimStatus = 'satisfied' | 'warning';
export type PolicyResult = 'pass' | 'block' | 'report-only';

export interface ValidationIssue {
  instancePath: string;
  schemaPath: string;
  keyword: string;
  message: string;
}

export interface ValidationResult {
  ok: boolean;
  errors: ValidationIssue[];
}

export interface CuratedSchemaRef {
  name: string;
  path: string;
  id: string | null;
  title: string | null;
}

export interface ArtifactMetadataOptions {
  now?: Date | string;
  env?: NodeJS.ProcessEnv;
  gitCommit?: string | null;
  branch?: string | null;
  runnerName?: string | null;
  runnerOs?: string | null;
  runnerArch?: string | null;
  ci?: boolean;
  toolVersions?: Record<string, string | undefined | null>;
}

export interface ArtifactMetadata {
  generatedAtUtc: string;
  generatedAtLocal: string;
  timezoneOffset: string;
  gitCommit: string | null;
  branch: string | null;
  runner: {
    name: string | null;
    os: string | null;
    arch: string | null;
    ci: boolean;
  };
  toolVersions: Record<string, string>;
}

export interface AssuranceProfileClaim {
  id: string;
  statement: string;
  kind: string;
  criticality: 'low' | 'medium' | 'high' | 'critical';
  targetLevel: 'A0' | 'A1' | 'A2' | 'A3' | 'A4';
  minIndependentSources?: number;
  requiredLanes: Lane[];
  requiredEvidenceKinds: string[];
}

export interface AssuranceProfile {
  schemaVersion: 'assurance-profile/v1';
  profileId: string;
  description?: string;
  deployment?: Record<string, unknown>;
  scope: {
    contextPackSources: string[];
    componentGlobs: string[];
  };
  claims: AssuranceProfileClaim[];
}

export interface EvidenceItem {
  claimId?: string;
  claimRefs?: string[];
  lane: Lane;
  kind: string;
  sourceKind?: SourceKind;
  origin?: string;
  status?: 'observed' | 'warning';
  artifactPath?: string | null;
  detail?: string | null;
  generatorLineage?: string | null;
}

export interface AggregateLanesOptions {
  profile: AssuranceProfile | string;
  evidence?: EvidenceItem[];
  generatedAt?: string | Date;
  metadata?: ArtifactMetadata;
  inputs?: Partial<AssuranceSummary['inputs']>;
  assuranceProfilePath?: string;
}

export interface AssuranceSummaryClaim {
  claimId: string;
  statement: string;
  criticality: AssuranceProfileClaim['criticality'];
  targetLevel: AssuranceProfileClaim['targetLevel'];
  minIndependentSources: number;
  observedIndependentSources: number;
  requiredLanes: Lane[];
  observedLanes: Lane[];
  missingLanes: Lane[];
  requiredEvidenceKinds: string[];
  observedEvidenceKinds: string[];
  missingEvidenceKinds: string[];
  counterexamples: {
    open: number;
    resolved: number;
    acceptedRisk: number;
    total: number;
  };
  independenceWarnings: string[];
  status: ClaimStatus;
  evidence: Array<Required<Pick<EvidenceItem, 'lane' | 'kind'>> & {
    sourceKind: SourceKind;
    origin: string;
    status: 'observed' | 'warning';
    artifactPath: string | null;
    detail: string | null;
    claimRefs: string[];
    generatorLineage: string | null;
  }>;
}

export interface AssuranceSummary {
  schemaVersion: 'assurance-summary/v1';
  generatedAt: string;
  metadata: ArtifactMetadata;
  inputs: {
    assuranceProfile: string;
    contextPacks: string[];
    verifyLiteSummary: string | null;
    formalSummaries: string[];
    conformanceReport: string | null;
    counterexamples: string[];
    evidenceManifests: string[];
    producerSummaries?: string[];
    boundaryMapSummaries?: string[];
    claimEvidenceManifests?: string[];
    policyDecision?: string | null;
    securityClaims?: string | null;
    securityFindings?: string | null;
    securityReview?: string | null;
  };
  summary: {
    claimCount: number;
    satisfiedClaims: number;
    warningClaims: number;
    claimsMissingRequiredLanes: number;
    claimsMissingRequiredEvidenceKinds: number;
    unlinkedCounterexamples: number;
    warningCount: number;
  };
  laneCoverage: Record<Lane, { requiredClaims: number; observedClaims: number }>;
  claims: AssuranceSummaryClaim[];
  warnings: Array<{ code: string; message: string; claimId?: string | null; artifactPath?: string | null }>;
}

export interface PolicyEvaluationOptions {
  policy: string | Record<string, unknown>;
  evidenceIds: string[];
  generatedAt?: string | Date;
  repository?: string;
  prNumber?: number;
  inputPath?: string;
  mode?: 'strict' | 'report-only';
}

export interface CorePolicyDecision {
  schemaVersion: 'core-policy-decision/v1';
  generatedAt: string;
  result: PolicyResult;
  mode: 'strict' | 'report-only';
  requiredEvidence: string[];
  observedEvidence: string[];
  missingEvidence: string[];
  repository: string | null;
  prNumber: number | null;
  inputPath: string | null;
}

export interface ReviewSurfaceOptions {
  title?: string;
  policyDecision?: CorePolicyDecision | null;
}

function readJsonFile(filePath: string): Record<string, unknown> {
  return JSON.parse(readFileSync(filePath, 'utf8')) as Record<string, unknown>;
}

function toIssue(error: ErrorObject): ValidationIssue {
  return {
    instancePath: error.instancePath,
    schemaPath: error.schemaPath,
    keyword: error.keyword,
    message: error.message ?? 'schema validation error',
  };
}

function createAjv(): Ajv2020 {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  for (const schemaFile of CURATED_SCHEMA_FILES) {
    const schema = readJsonFile(path.join(schemaRoot, schemaFile));
    if (schema.$id && typeof schema.$id === 'string') {
      ajv.addSchema(schema);
    }
  }
  return ajv;
}

function schemaNameToFile(schemaName: string): string {
  const normalized = schemaName.endsWith('.schema.json') ? schemaName : `${schemaName}.schema.json`;
  if (!CURATED_SCHEMA_FILES.includes(normalized as (typeof CURATED_SCHEMA_FILES)[number])) {
    throw new Error(`Unknown curated schema: ${schemaName}`);
  }
  return normalized;
}

function normalizeValidation(validate: ValidateFunction, data: unknown): ValidationResult {
  const ok = validate(data) === true;
  return {
    ok,
    errors: ok ? [] : (validate.errors ?? []).map(toIssue),
  };
}

export function listCuratedSchemas(): CuratedSchemaRef[] {
  return CURATED_SCHEMA_FILES.map((schemaFile) => {
    const schema = readJsonFile(path.join(schemaRoot, schemaFile));
    return {
      name: schemaFile,
      path: `schema/${schemaFile}`,
      id: typeof schema.$id === 'string' ? schema.$id : null,
      title: typeof schema.title === 'string' ? schema.title : null,
    };
  });
}

export function validateWithSchema(schemaName: string, data: unknown): ValidationResult {
  const ajv = createAjv();
  const schemaFile = schemaNameToFile(schemaName);
  const schema = readJsonFile(path.join(schemaRoot, schemaFile));
  const schemaId = typeof schema.$id === 'string' ? schema.$id : null;
  const validate = (schemaId ? ajv.getSchema(schemaId) : null) ?? ajv.compile(schema);
  return normalizeValidation(validate, data);
}

export function parseYamlOrJson(input: string): unknown {
  const trimmed = input.trim();
  if (!trimmed) {
    throw new Error('Cannot parse an empty document');
  }
  if (trimmed.startsWith('{') || trimmed.startsWith('[')) {
    return JSON.parse(trimmed);
  }
  return yaml.parse(trimmed);
}

export function parseProfile(input: string | AssuranceProfile): AssuranceProfile {
  if (typeof input === 'string') {
    return parseYamlOrJson(input) as AssuranceProfile;
  }
  return input;
}

export function validateProfile(profile: string | AssuranceProfile): ValidationResult {
  return validateWithSchema('assurance-profile', parseProfile(profile));
}

const pad2 = (value: number): string => String(value).padStart(2, '0');
const pad3 = (value: number): string => String(value).padStart(3, '0');

function formatOffset(minutes: number): string {
  const sign = minutes <= 0 ? '+' : '-';
  const abs = Math.abs(minutes);
  return `${sign}${pad2(Math.floor(abs / 60))}:${pad2(abs % 60)}`;
}

function formatLocalIso(date: Date): string {
  return `${date.getFullYear()}-${pad2(date.getMonth() + 1)}-${pad2(date.getDate())}`
    + `T${pad2(date.getHours())}:${pad2(date.getMinutes())}:${pad2(date.getSeconds())}`
    + `.${pad3(date.getMilliseconds())}${formatOffset(date.getTimezoneOffset())}`;
}

function normalizeDate(value: Date | string | undefined): Date {
  if (value instanceof Date) return value;
  if (typeof value === 'string') return new Date(value);
  return new Date();
}

function compactToolVersions(values: Record<string, string | undefined | null>): Record<string, string> {
  const entries = Object.entries(values)
    .map(([key, value]) => [key, String(value ?? '').trim()] as const)
    .filter(([, value]) => value.length > 0);
  return Object.fromEntries(entries);
}

export function buildArtifactMetadata(options: ArtifactMetadataOptions = {}): ArtifactMetadata {
  const env = options.env ?? process.env;
  const now = normalizeDate(options.now);
  const toolVersions = compactToolVersions({ node: process.version, ...(options.toolVersions ?? {}) });
  return {
    generatedAtUtc: now.toISOString(),
    generatedAtLocal: formatLocalIso(now),
    timezoneOffset: formatOffset(now.getTimezoneOffset()),
    gitCommit: options.gitCommit ?? env.GIT_COMMIT ?? env.GITHUB_SHA ?? null,
    branch: options.branch ?? env.GITHUB_HEAD_REF ?? env.GITHUB_REF_NAME ?? env.BRANCH_NAME ?? null,
    runner: {
      name: options.runnerName ?? env.RUNNER_NAME ?? env.HOSTNAME ?? null,
      os: options.runnerOs ?? env.RUNNER_OS ?? process.platform,
      arch: options.runnerArch ?? env.RUNNER_ARCH ?? process.arch,
      ci: options.ci ?? env.CI === 'true',
    },
    toolVersions,
  };
}

function uniqueSorted<T extends string>(values: Iterable<T>): T[] {
  return Array.from(new Set(values)).sort();
}

function claimEvidence(evidence: EvidenceItem[], claimId: string): EvidenceItem[] {
  return evidence.filter((item) => item.claimId === claimId || item.claimRefs?.includes(claimId));
}

function defaultMinIndependentSources(claim: AssuranceProfileClaim): number {
  if (claim.minIndependentSources && claim.minIndependentSources > 0) return claim.minIndependentSources;
  return claim.criticality === 'high' || claim.criticality === 'critical' ? 2 : 1;
}

function buildLaneCoverage(claims: AssuranceSummaryClaim[]): AssuranceSummary['laneCoverage'] {
  const coverage = Object.fromEntries(
    LANE_ORDER.map((lane) => [lane, { requiredClaims: 0, observedClaims: 0 }]),
  ) as AssuranceSummary['laneCoverage'];
  for (const claim of claims) {
    for (const lane of claim.requiredLanes) coverage[lane].requiredClaims += 1;
    for (const lane of claim.observedLanes) coverage[lane].observedClaims += 1;
  }
  return coverage;
}

export function aggregateLanes(options: AggregateLanesOptions): AssuranceSummary {
  const profile = parseProfile(options.profile);
  const generatedAt = normalizeDate(options.generatedAt).toISOString();
  const evidence = options.evidence ?? [];
  const claims = profile.claims.map((claim) => {
    const matchingEvidence = claimEvidence(evidence, claim.id);
    const observedLanes = uniqueSorted(matchingEvidence.map((item) => item.lane));
    const observedEvidenceKinds = uniqueSorted(matchingEvidence.map((item) => item.kind));
    const requiredLanes = uniqueSorted(claim.requiredLanes);
    const requiredEvidenceKinds = uniqueSorted(claim.requiredEvidenceKinds);
    const missingLanes = requiredLanes.filter((lane) => !observedLanes.includes(lane));
    const missingEvidenceKinds = requiredEvidenceKinds.filter((kind) => !observedEvidenceKinds.includes(kind));
    const observedIndependentSources = new Set(
      matchingEvidence.map((item) => `${item.sourceKind ?? 'unknown'}:${item.generatorLineage ?? item.origin ?? 'unknown'}`),
    ).size;
    const minIndependentSources = defaultMinIndependentSources(claim);
    const independenceWarnings = observedIndependentSources < minIndependentSources
      ? ['insufficient-independent-lanes']
      : [];
    const status: ClaimStatus = missingLanes.length > 0
      || missingEvidenceKinds.length > 0
      || independenceWarnings.length > 0
      ? 'warning'
      : 'satisfied';
    return {
      claimId: claim.id,
      statement: claim.statement,
      criticality: claim.criticality,
      targetLevel: claim.targetLevel,
      minIndependentSources,
      observedIndependentSources,
      requiredLanes,
      observedLanes,
      missingLanes,
      requiredEvidenceKinds,
      observedEvidenceKinds,
      missingEvidenceKinds,
      counterexamples: { open: 0, resolved: 0, acceptedRisk: 0, total: 0 },
      independenceWarnings,
      status,
      evidence: matchingEvidence.map((item) => ({
        lane: item.lane,
        kind: item.kind,
        sourceKind: item.sourceKind ?? 'unknown',
        origin: item.origin ?? 'core',
        status: item.status ?? 'observed',
        artifactPath: item.artifactPath ?? null,
        detail: item.detail ?? null,
        claimRefs: item.claimRefs ?? [claim.id],
        generatorLineage: item.generatorLineage ?? null,
      })),
    } satisfies AssuranceSummaryClaim;
  });
  const warnings = claims.flatMap((claim) => [
    ...claim.missingLanes.map((lane) => ({
      code: 'insufficient-independent-lanes',
      message: `Claim ${claim.claimId} is missing required lane ${lane}.`,
      claimId: claim.claimId,
      artifactPath: null,
    })),
    ...claim.missingEvidenceKinds.map((kind) => ({
      code: 'unrecognized-evidence-claim',
      message: `Claim ${claim.claimId} is missing required evidence kind ${kind}.`,
      claimId: claim.claimId,
      artifactPath: null,
    })),
    ...claim.independenceWarnings.map((code) => ({
      code,
      message: `Claim ${claim.claimId} has insufficient independent evidence sources.`,
      claimId: claim.claimId,
      artifactPath: null,
    })),
  ]);
  return {
    schemaVersion: 'assurance-summary/v1',
    generatedAt,
    metadata: options.metadata ?? buildArtifactMetadata({ now: generatedAt }),
    inputs: {
      assuranceProfile: options.assuranceProfilePath ?? profile.profileId,
      contextPacks: [],
      verifyLiteSummary: null,
      formalSummaries: [],
      conformanceReport: null,
      counterexamples: [],
      evidenceManifests: [],
      ...(options.inputs ?? {}),
    },
    summary: {
      claimCount: claims.length,
      satisfiedClaims: claims.filter((claim) => claim.status === 'satisfied').length,
      warningClaims: claims.filter((claim) => claim.status === 'warning').length,
      claimsMissingRequiredLanes: claims.filter((claim) => claim.missingLanes.length > 0).length,
      claimsMissingRequiredEvidenceKinds: claims.filter((claim) => claim.missingEvidenceKinds.length > 0).length,
      unlinkedCounterexamples: 0,
      warningCount: warnings.length,
    },
    laneCoverage: buildLaneCoverage(claims),
    claims,
    warnings,
  };
}

export function evaluatePolicyGate(options: PolicyEvaluationOptions): CorePolicyDecision {
  const policy = typeof options.policy === 'string'
    ? parseYamlOrJson(options.policy) as Record<string, unknown>
    : options.policy;
  const requiredEvidence = Array.isArray(policy.requiredEvidence)
    ? policy.requiredEvidence.map((value) => String(value))
    : [];
  const observedEvidence = uniqueSorted(options.evidenceIds);
  const missingEvidence = requiredEvidence.filter((evidenceId) => !observedEvidence.includes(evidenceId));
  const mode = options.mode ?? 'strict';
  const result: PolicyResult = missingEvidence.length === 0 ? 'pass' : (mode === 'strict' ? 'block' : 'report-only');
  return {
    schemaVersion: 'core-policy-decision/v1',
    generatedAt: normalizeDate(options.generatedAt).toISOString(),
    result,
    mode,
    requiredEvidence,
    observedEvidence,
    missingEvidence,
    repository: options.repository ?? null,
    prNumber: options.prNumber ?? null,
    inputPath: options.inputPath ?? null,
  };
}

export function renderReviewSurface(summary: AssuranceSummary, options: ReviewSurfaceOptions = {}): string {
  const title = options.title ?? 'PR Assurance Review Surface';
  const lines = [
    `# ${title}`,
    '',
    `- Profile: ${summary.inputs.assuranceProfile}`,
    `- Claims: ${summary.summary.satisfiedClaims}/${summary.summary.claimCount} satisfied`,
    `- Warnings: ${summary.summary.warningCount}`,
  ];
  if (options.policyDecision) {
    lines.push(`- Policy decision: ${options.policyDecision.result} (${options.policyDecision.mode})`);
  }
  lines.push('', '| Claim | Status | Missing lanes | Missing evidence |', '| --- | --- | --- | --- |');
  for (const claim of summary.claims) {
    lines.push(`| ${claim.claimId} | ${claim.status} | ${claim.missingLanes.join(', ') || 'none'} | ${claim.missingEvidenceKinds.join(', ') || 'none'} |`);
  }
  if (summary.warnings.length > 0) {
    lines.push('', '## Warnings');
    for (const warning of summary.warnings) {
      lines.push(`- ${warning.code}: ${warning.message}`);
    }
  }
  return `${lines.join('\n')}\n`;
}
