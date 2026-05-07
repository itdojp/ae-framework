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

type JsonRecord = Record<string, unknown>;
type AuditTaskStatus = 'ready' | 'blocked-no-candidate-location' | 'blocked-missing-code-map';
type Severity = 'low' | 'medium' | 'high' | 'critical';
type Confidence = 'low' | 'medium' | 'high';
type ResponseResult = 'finding' | 'no-finding';
type AuditOutcomeResult = 'finding' | 'no-finding' | 'missing-response';

type SecurityClaim = {
  id: string;
  statement: string;
  criticality?: Severity;
  trustBoundary?: JsonRecord;
};

type SecurityClaimDocument = {
  schemaVersion: 'security-claim/v1';
  generatedAt?: string;
  claims: SecurityClaim[];
};

type SecurityAuditScopeDocument = {
  schemaVersion: 'security-audit-scope/v1';
  generatedAt?: string;
  trustBoundaries?: Array<{ id?: string; name?: string; entryPoints?: string[]; attackerControlled?: boolean }>;
};

type CodeMapCandidateLocation = {
  path: string;
  startLine: number;
  endLine: number;
  symbol?: string;
  reason: string;
  matchedTerms?: string[];
};

type CodeMapMapping = {
  claimId: string;
  candidateLocations: CodeMapCandidateLocation[];
};

type SecurityCodeMapDocument = {
  schemaVersion: 'security-code-map/v1';
  generatedAt?: string;
  mappings: CodeMapMapping[];
};

export interface AuditWarning {
  code: string;
  source?: string;
  path: string;
  message: string;
}

export interface AuditCandidateLocation {
  path: string;
  startLine: number;
  endLine: number;
  symbol?: string;
  reason: string;
  matchedTerms?: string[];
}

export interface ProofAttemptPrompt {
  map: string;
  prove: string;
  stressTest: string;
  report: string;
}

export interface SecurityAuditTask {
  id: string;
  claimId: string;
  claimStatement: string;
  status: AuditTaskStatus;
  candidateLocations: AuditCandidateLocation[];
  scopeRefs: string[];
  proofAttemptPrompt: ProofAttemptPrompt;
  warnings: AuditWarning[];
}

export interface SecurityAuditTaskBundleDocument {
  schemaVersion: 'security-audit-task-bundle/v1';
  generatedAt: string;
  tasks: SecurityAuditTask[];
  summary: {
    totalTasks: number;
    readyTasks: number;
    blockedTasks: number;
    totalCandidateLocations: number;
    totalWarnings: number;
    byStatus: {
      ready: number;
      blockedNoCandidateLocation: number;
      blockedMissingCodeMap: number;
    };
  };
  provenance: {
    origin: 'deterministic' | 'fixture';
    generator: string;
    claims: string;
    codeMap: string;
    scope: string;
  };
  warnings: AuditWarning[];
}

export interface SecurityFindingDocument {
  schemaVersion: 'security-finding/v1';
  generatedAt: string;
  findings: JsonRecord[];
  summary: {
    totalFindings: number;
    byStatus: Record<'candidate' | 'needsHumanReview' | 'confirmed' | 'rejected' | 'waived' | 'outOfScope', number>;
    bySeverity: Record<Severity, number>;
  };
}

export interface SecurityAuditResponseFixture {
  schemaVersion: 'security-audit-response-fixture/v1';
  responses: SecurityAuditResponse[];
}

export interface SecurityAuditResponse {
  taskId?: string;
  claimId?: string;
  result: ResponseResult;
  finding?: JsonRecord;
  rationale?: string;
}

export interface SecurityAuditOptions {
  generatedAt?: string;
  repoRoot?: string;
  validate?: boolean;
  responseFixture?: string;
}

export interface SecurityAuditOutputPaths {
  tasks: string;
  summaryMarkdown: string;
  findings?: string;
}

export interface SecurityAuditOutcome {
  taskId: string;
  claimId: string;
  result: AuditOutcomeResult;
  findingIds: string[];
  rationale?: string;
}

export interface SecurityAuditResult {
  generatedAt: string;
  taskBundle: SecurityAuditTaskBundleDocument;
  findings?: SecurityFindingDocument;
  warnings: AuditWarning[];
  outputPaths: SecurityAuditOutputPaths;
  responseSummary: {
    totalResponses: number;
    findingResponses: number;
    noFindingResponses: number;
    missingResponses: number;
  };
  auditOutcomes: SecurityAuditOutcome[];
}

const GENERATOR = 'security-proof-attempt-audit';
const MODULE_DIR = path.dirname(fileURLToPath(import.meta.url));
const SEVERITIES: readonly Severity[] = ['low', 'medium', 'high', 'critical'];
const CONFIDENCE: readonly Confidence[] = ['low', 'medium', 'high'];

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

function formatId(prefix: string, index: number): string {
  return `${prefix}-${String(index + 1).padStart(3, '0')}`;
}

function warning(code: string, pathRef: string, message: string, source?: string): AuditWarning {
  return {
    code,
    ...(source !== undefined ? { source } : {}),
    path: pathRef,
    message,
  };
}

function portablePathFrom(baseDir: string, targetPath: string): string {
  return normalizeArtifactPath(targetPath, { repoRoot: baseDir }) ?? targetPath.replace(/\\/g, '/');
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
    if (existsSync(path.join(candidate, 'schema/security-audit-task-bundle-v1.schema.json'))) {
      return candidate;
    }
  }
  throw new Error('Unable to locate ae-framework schema directory for security audit validation.');
}

function outputPathsFor(outPath: string, includeFindings: boolean): SecurityAuditOutputPaths {
  const resolvedOut = path.resolve(outPath);
  if (path.extname(resolvedOut).toLowerCase() === '.json') {
    return {
      tasks: path.join(path.dirname(resolvedOut), 'security-audit-tasks.json'),
      summaryMarkdown: path.join(path.dirname(resolvedOut), 'security-audit-summary.md'),
      ...(includeFindings ? { findings: resolvedOut } : {}),
    };
  }
  return {
    tasks: path.join(resolvedOut, 'security-audit-tasks.json'),
    summaryMarkdown: path.join(resolvedOut, 'security-audit-summary.md'),
    ...(includeFindings ? { findings: path.join(resolvedOut, 'security-findings.json') } : {}),
  };
}

async function loadJson(filePath: string): Promise<unknown> {
  return JSON.parse(await fs.readFile(filePath, 'utf8')) as unknown;
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

function parseClaims(document: unknown): SecurityClaimDocument {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-claim/v1' || !Array.isArray(document['claims'])) {
    throw new Error('Expected security-claim/v1 document with a claims array.');
  }
  const claims = document['claims'].map((rawClaim, index) => {
    if (!isRecord(rawClaim)) {
      throw new Error(`Security claim at index ${index} must be an object.`);
    }
    const id = asString(rawClaim['id']);
    if (!id) {
      throw new Error(`Security claim at index ${index} must have a non-empty id.`);
    }
    const statement = asString(rawClaim['statement']) ?? `Security claim ${id}`;
    const parsed: SecurityClaim = { id, statement };
    const criticality = normalizeSeverity(rawClaim['criticality']);
    if (criticality !== undefined) {
      parsed.criticality = criticality;
    }
    if (isRecord(rawClaim['trustBoundary'])) {
      parsed.trustBoundary = rawClaim['trustBoundary'];
    }
    return parsed;
  });
  const parsedDocument: SecurityClaimDocument = { schemaVersion: 'security-claim/v1', claims };
  const generatedAt = asString(document['generatedAt']);
  if (generatedAt !== undefined) {
    parsedDocument.generatedAt = generatedAt;
  }
  return parsedDocument;
}

function parseCodeMap(document: unknown): SecurityCodeMapDocument {
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
      ? rawMapping['candidateLocations'].map((rawLocation, locationIndex) => parseCandidateLocation(rawLocation, `/mappings/${mappingIndex}/candidateLocations/${locationIndex}`))
      : [];
    return { claimId, candidateLocations };
  });
  const parsedDocument: SecurityCodeMapDocument = { schemaVersion: 'security-code-map/v1', mappings };
  const generatedAt = asString(document['generatedAt']);
  if (generatedAt !== undefined) {
    parsedDocument.generatedAt = generatedAt;
  }
  return parsedDocument;
}

function parseScope(document: unknown): SecurityAuditScopeDocument {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-audit-scope/v1') {
    throw new Error('Expected security-audit-scope/v1 document.');
  }
  const parsedScope: SecurityAuditScopeDocument = { schemaVersion: 'security-audit-scope/v1' };
  const generatedAt = asString(document['generatedAt']);
  if (generatedAt !== undefined) {
    parsedScope.generatedAt = generatedAt;
  }
  if (Array.isArray(document['trustBoundaries'])) {
    parsedScope.trustBoundaries = document['trustBoundaries'].filter(isRecord).map((boundary) => {
      const parsed: { id?: string; name?: string; entryPoints?: string[]; attackerControlled?: boolean } = {};
      const id = asString(boundary['id']);
      if (id !== undefined) {
        parsed.id = id;
      }
      const name = asString(boundary['name']);
      if (name !== undefined) {
        parsed.name = name;
      }
      const entryPoints = asStringArray(boundary['entryPoints']);
      if (entryPoints.length > 0) {
        parsed.entryPoints = unique(entryPoints);
      }
      if (typeof boundary['attackerControlled'] === 'boolean') {
        parsed.attackerControlled = boundary['attackerControlled'];
      }
      return parsed;
    });
  }
  return parsedScope;
}

function parseCandidateLocation(rawLocation: unknown, pathRef: string): AuditCandidateLocation {
  if (!isRecord(rawLocation)) {
    throw new Error(`Candidate location ${pathRef} must be an object.`);
  }
  const candidatePath = asString(rawLocation['path']);
  if (!candidatePath) {
    throw new Error(`Candidate location ${pathRef} must have a non-empty path.`);
  }
  const startLine = typeof rawLocation['startLine'] === 'number' ? Math.max(1, Math.floor(rawLocation['startLine'])) : 1;
  const rawEndLine = typeof rawLocation['endLine'] === 'number' ? Math.max(1, Math.floor(rawLocation['endLine'])) : startLine;
  const endLine = Math.max(startLine, rawEndLine);
  const reason = asString(rawLocation['reason']) ?? 'Candidate location supplied by security-code-map/v1.';
  const parsed: AuditCandidateLocation = { path: candidatePath, startLine, endLine, reason };
  const symbol = asString(rawLocation['symbol']);
  if (symbol !== undefined) {
    parsed.symbol = symbol;
  }
  const matchedTerms = unique(asStringArray(rawLocation['matchedTerms']));
  if (matchedTerms.length > 0) {
    parsed.matchedTerms = matchedTerms;
  }
  return parsed;
}

function normalizeSeverity(value: unknown): Severity | undefined {
  const candidate = asString(value)?.toLowerCase();
  if (candidate && (SEVERITIES as readonly string[]).includes(candidate)) {
    return candidate as Severity;
  }
  return undefined;
}

function normalizeConfidence(value: unknown): Confidence | undefined {
  const candidate = asString(value)?.toLowerCase();
  if (candidate && (CONFIDENCE as readonly string[]).includes(candidate)) {
    return candidate as Confidence;
  }
  return undefined;
}

function taskStatusSummaryKey(status: AuditTaskStatus): keyof SecurityAuditTaskBundleDocument['summary']['byStatus'] {
  if (status === 'blocked-no-candidate-location') {
    return 'blockedNoCandidateLocation';
  }
  if (status === 'blocked-missing-code-map') {
    return 'blockedMissingCodeMap';
  }
  return 'ready';
}

function lineRef(location: AuditCandidateLocation): string {
  const symbol = location.symbol ? ` (${location.symbol})` : '';
  return `${location.path}:${location.startLine}-${location.endLine}${symbol}`;
}

function scopeRefsForClaim(claim: SecurityClaim, scope: SecurityAuditScopeDocument): string[] {
  const fromClaim = claim.trustBoundary
    ? unique([...asStringArray(claim.trustBoundary['boundaryIds']), ...asStringArray(claim.trustBoundary['id']), ...asStringArray(claim.trustBoundary['entryPoints'])])
    : [];
  if (fromClaim.length > 0) {
    return fromClaim;
  }
  const fromScope = unique((scope.trustBoundaries ?? []).flatMap((boundary) => [boundary.id, boundary.name].filter((entry): entry is string => Boolean(entry))));
  return fromScope.length > 0 ? fromScope : ['security-audit-scope'];
}

function promptForTask(claim: SecurityClaim, candidateLocations: AuditCandidateLocation[]): ProofAttemptPrompt {
  const mapped = candidateLocations.length > 0
    ? candidateLocations.map((location) => `- ${lineRef(location)}: ${location.reason}`).join('\n')
    : '- No candidate code location was resolved for this claim.';
  return {
    map: `Map the security claim to these candidate code paths:\n${mapped}`,
    prove: `Prove whether the implementation satisfies claim ${claim.id}: ${claim.statement}`,
    stressTest: 'Stress-test attacker-controlled inputs, trust-boundary assumptions, cache/key equivalence classes, and edge cases that could break the proof. Do not generate exploit automation.',
    report: 'Report a candidate finding only when the proof fails with concrete code evidence. Keep all findings as candidate status until three-gate review.',
  };
}

function buildTask(
  claim: SecurityClaim,
  claimIndex: number,
  codeMapByClaim: Map<string, CodeMapMapping>,
  scope: SecurityAuditScopeDocument,
): SecurityAuditTask {
  const mapping = codeMapByClaim.get(claim.id);
  const candidateLocations = mapping?.candidateLocations ?? [];
  const status: AuditTaskStatus = !mapping
    ? 'blocked-missing-code-map'
    : candidateLocations.length === 0
      ? 'blocked-no-candidate-location'
      : 'ready';
  const warnings: AuditWarning[] = [];
  if (!mapping) {
    warnings.push(warning('missing-code-map', `/tasks/${claimIndex}/candidateLocations`, `No security-code-map/v1 mapping was found for ${claim.id}.`));
  } else if (candidateLocations.length === 0) {
    warnings.push(warning('no-candidate-location', `/tasks/${claimIndex}/candidateLocations`, `No candidate code location was resolved for ${claim.id}.`));
  }
  return {
    id: formatId('SEC-AUDIT-TASK', claimIndex),
    claimId: claim.id,
    claimStatement: claim.statement,
    status,
    candidateLocations,
    scopeRefs: scopeRefsForClaim(claim, scope),
    proofAttemptPrompt: promptForTask(claim, candidateLocations),
    warnings,
  };
}

function summarizeTasks(tasks: SecurityAuditTask[], documentWarnings: AuditWarning[]): SecurityAuditTaskBundleDocument['summary'] {
  const byStatus = { ready: 0, blockedNoCandidateLocation: 0, blockedMissingCodeMap: 0 };
  let totalCandidateLocations = 0;
  let taskWarnings = 0;
  for (const task of tasks) {
    byStatus[taskStatusSummaryKey(task.status)] += 1;
    totalCandidateLocations += task.candidateLocations.length;
    taskWarnings += task.warnings.length;
  }
  return {
    totalTasks: tasks.length,
    readyTasks: byStatus.ready,
    blockedTasks: tasks.length - byStatus.ready,
    totalCandidateLocations,
    totalWarnings: documentWarnings.length + taskWarnings,
    byStatus,
  };
}

export function buildSecurityAuditTaskBundle(
  claims: SecurityClaimDocument,
  codeMap: SecurityCodeMapDocument,
  scope: SecurityAuditScopeDocument,
  generatedAt: string,
  provenance: SecurityAuditTaskBundleDocument['provenance'],
): SecurityAuditTaskBundleDocument {
  const warnings: AuditWarning[] = [];
  const codeMapByClaim = new Map(codeMap.mappings.map((mapping) => [mapping.claimId, mapping]));
  const tasks = claims.claims.map((claim, index) => buildTask(claim, index, codeMapByClaim, scope));
  return {
    schemaVersion: 'security-audit-task-bundle/v1',
    generatedAt,
    tasks,
    summary: summarizeTasks(tasks, warnings),
    provenance,
    warnings,
  };
}

function parseResponseFixture(document: unknown): SecurityAuditResponseFixture {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-audit-response-fixture/v1' || !Array.isArray(document['responses'])) {
    throw new Error('Expected security-audit-response-fixture/v1 document with a responses array.');
  }
  return {
    schemaVersion: 'security-audit-response-fixture/v1',
    responses: document['responses'].map((rawResponse, index) => {
      if (!isRecord(rawResponse)) {
        throw new Error(`Security audit response at index ${index} must be an object.`);
      }
      const result = asString(rawResponse['result']);
      if (result !== 'finding' && result !== 'no-finding') {
        throw new Error(`Security audit response at index ${index} must use result 'finding' or 'no-finding'.`);
      }
      const parsed: SecurityAuditResponse = { result };
      const taskId = asString(rawResponse['taskId']);
      if (taskId !== undefined) {
        parsed.taskId = taskId;
      }
      const claimId = asString(rawResponse['claimId']);
      if (claimId !== undefined) {
        parsed.claimId = claimId;
      }
      if (isRecord(rawResponse['finding'])) {
        parsed.finding = rawResponse['finding'];
      }
      const rationale = asString(rawResponse['rationale']);
      if (rationale !== undefined) {
        parsed.rationale = rationale;
      }
      return parsed;
    }),
  };
}

function countFindingStatus(): SecurityFindingDocument['summary']['byStatus'] {
  return { candidate: 0, needsHumanReview: 0, confirmed: 0, rejected: 0, waived: 0, outOfScope: 0 };
}

function countSeverity(): Record<Severity, number> {
  return { low: 0, medium: 0, high: 0, critical: 0 };
}

function normalizeAffectedLocations(raw: unknown, task: SecurityAuditTask, pathRef: string, warnings: AuditWarning[]): JsonRecord[] {
  const rawLocations = Array.isArray(raw) ? raw : task.candidateLocations;
  if (rawLocations.length === 0) {
    warnings.push(warning('missing-affected-location', pathRef, `Finding response for ${task.claimId} had no affected location; emitted a placeholder.`));
    return [{ path: 'unmapped', startLine: 1, endLine: 1, description: 'No mapped location was available for this candidate finding.' }];
  }
  return rawLocations.map((rawLocation, index) => {
    const location = parseCandidateLocation(rawLocation, `${pathRef}/${index}`);
    return {
      path: location.path,
      startLine: location.startLine,
      endLine: location.endLine,
      ...(location.symbol !== undefined ? { symbol: location.symbol } : {}),
      description: location.reason,
    };
  });
}

function normalizeEvidenceRefs(raw: unknown, task: SecurityAuditTask, taskBundlePath: string | undefined, codeMapPath: string | undefined): JsonRecord[] {
  if (Array.isArray(raw) && raw.every(isRecord)) {
    return raw.map((entry, index) => ({
      id: asString(entry['id']) ?? `SEC-EVIDENCE-${String(index + 1).padStart(3, '0')}`,
      kind: asString(entry['kind']) ?? 'manual',
      path: asString(entry['path']) ?? taskBundlePath ?? 'security-audit-tasks.json',
      ...(asString(entry['description']) ? { description: asString(entry['description']) } : {}),
    }));
  }
  return [
    {
      id: `SEC-EVIDENCE-${task.id}`,
      kind: 'audit-task',
      path: taskBundlePath ?? 'security-audit-tasks.json',
      description: `Proof-attempt audit task for ${task.claimId}.`,
    },
    {
      id: `SEC-CODE-MAP-${task.claimId}`,
      kind: 'security-code-map',
      path: codeMapPath ?? 'security-code-map.json',
      description: `Candidate source locations for ${task.claimId}.`,
    },
  ];
}

function proofAttemptFromResponse(raw: unknown, task: SecurityAuditTask, claimId: string): JsonRecord {
  const proofAttempt = isRecord(raw) ? raw : {};
  return {
    claim: asString(proofAttempt['claim']) ?? claimId,
    map: asString(proofAttempt['map']) ?? task.proofAttemptPrompt.map,
    prove: asString(proofAttempt['prove']) ?? task.proofAttemptPrompt.prove,
    stressTest: asString(proofAttempt['stressTest']) ?? task.proofAttemptPrompt.stressTest,
    report: asString(proofAttempt['report']) ?? task.proofAttemptPrompt.report,
  };
}

function findingFromResponse(
  response: SecurityAuditResponse,
  task: SecurityAuditTask,
  index: number,
  generatedAt: string,
  taskBundlePath: string | undefined,
  codeMapPath: string | undefined,
  warnings: AuditWarning[],
): JsonRecord {
  const rawFinding = response.finding ?? {};
  const rawStatus = asString(rawFinding['status']);
  if (rawStatus && rawStatus !== 'candidate') {
    warnings.push(warning('finding-status-normalized', `/responses/${index}/finding/status`, `Fixture status '${rawStatus}' was normalized to candidate.`));
  }
  const severity = normalizeSeverity(rawFinding['severity']) ?? 'medium';
  const confidence = normalizeConfidence(rawFinding['confidence']) ?? 'medium';
  const affectedLocations = normalizeAffectedLocations(rawFinding['affectedLocations'], task, `/responses/${index}/finding/affectedLocations`, warnings);
  return {
    id: asString(rawFinding['id']) ?? formatId('SEC-FINDING', index),
    claimId: task.claimId,
    status: 'candidate',
    severity,
    confidence,
    title: asString(rawFinding['title']) ?? `Proof attempt could not establish ${task.claimId}`,
    summary: asString(rawFinding['summary']) ?? response.rationale ?? `The simulated proof attempt reported a candidate gap for ${task.claimId}.`,
    affectedLocations,
    proofAttempt: proofAttemptFromResponse(rawFinding['proofAttempt'], task, task.claimId),
    scopeRefs: unique(asStringArray(rawFinding['scopeRefs']).length > 0 ? asStringArray(rawFinding['scopeRefs']) : task.scopeRefs),
    evidenceRefs: normalizeEvidenceRefs(rawFinding['evidenceRefs'], task, taskBundlePath, codeMapPath),
    provenance: {
      origin: 'fixture',
      generator: GENERATOR,
      source: 'security-audit-response-fixture/v1',
      version: generatedAt,
    },
    notes: unique(['Candidate finding is not a confirmed vulnerability.', ...asStringArray(rawFinding['notes'])]),
  };
}

export function normalizeAuditResponsesToFindings(
  responseFixture: SecurityAuditResponseFixture,
  taskBundle: SecurityAuditTaskBundleDocument,
  generatedAt: string,
  options: { taskBundlePath?: string; codeMapPath?: string } = {},
): { findings: SecurityFindingDocument; warnings: AuditWarning[]; responseSummary: SecurityAuditResult['responseSummary']; auditOutcomes: SecurityAuditOutcome[] } {
  const warnings: AuditWarning[] = [];
  const taskById = new Map(taskBundle.tasks.map((task) => [task.id, task]));
  const taskByClaimId = new Map(taskBundle.tasks.map((task) => [task.claimId, task]));
  const findings: JsonRecord[] = [];
  const respondedTaskIds = new Set<string>();
  const outcomeByTaskId = new Map<string, SecurityAuditOutcome>();
  let noFindingResponses = 0;
  for (const [index, response] of responseFixture.responses.entries()) {
    const task = (response.taskId ? taskById.get(response.taskId) : undefined) ?? (response.claimId ? taskByClaimId.get(response.claimId) : undefined);
    if (!task) {
      warnings.push(warning('orphan-response', `/responses/${index}`, 'Security audit response did not match any generated audit task.'));
      continue;
    }
    respondedTaskIds.add(task.id);
    const outcome = outcomeByTaskId.get(task.id) ?? {
      taskId: task.id,
      claimId: task.claimId,
      result: response.result,
      findingIds: [],
      ...(response.rationale !== undefined ? { rationale: response.rationale } : {}),
    };
    if (response.result === 'no-finding') {
      noFindingResponses += 1;
      outcome.result = 'no-finding';
      if (response.rationale !== undefined) {
        outcome.rationale = response.rationale;
      }
      outcomeByTaskId.set(task.id, outcome);
      continue;
    }
    const finding = findingFromResponse(response, task, findings.length, generatedAt, options.taskBundlePath, options.codeMapPath, warnings);
    findings.push(finding);
    outcome.result = 'finding';
    const findingId = asString(finding['id']);
    if (findingId !== undefined) {
      outcome.findingIds.push(findingId);
    }
    outcomeByTaskId.set(task.id, outcome);
  }
  if (findings.length === 0) {
    throw new Error('Security audit response fixture did not produce any security-finding/v1 findings; omit responseFixture for dry-run task generation only.');
  }
  const byStatus = countFindingStatus();
  const bySeverity = countSeverity();
  for (const finding of findings) {
    byStatus.candidate += 1;
    const severity = normalizeSeverity(finding['severity']) ?? 'medium';
    bySeverity[severity] += 1;
  }
  const findingsDocument: SecurityFindingDocument = {
    schemaVersion: 'security-finding/v1',
    generatedAt,
    findings,
    summary: {
      totalFindings: findings.length,
      byStatus,
      bySeverity,
    },
  };
  const auditOutcomes = taskBundle.tasks.map((task) => outcomeByTaskId.get(task.id) ?? {
    taskId: task.id,
    claimId: task.claimId,
    result: 'missing-response' as const,
    findingIds: [],
  });
  return {
    findings: findingsDocument,
    warnings,
    responseSummary: {
      totalResponses: responseFixture.responses.length,
      findingResponses: findings.length,
      noFindingResponses,
      missingResponses: taskBundle.tasks.filter((task) => !respondedTaskIds.has(task.id)).length,
    },
    auditOutcomes,
  };
}


function renderSummaryMarkdown(result: SecurityAuditResult): string {
  const lines = [
    '# Security proof-attempt audit summary',
    '',
    `- Generated at: ${result.generatedAt}`,
    `- Audit tasks: ${result.taskBundle.summary.totalTasks}`,
    `- Ready tasks: ${result.taskBundle.summary.readyTasks}`,
    `- Blocked tasks: ${result.taskBundle.summary.blockedTasks}`,
    `- Candidate locations: ${result.taskBundle.summary.totalCandidateLocations}`,
    `- Findings generated: ${result.findings?.summary.totalFindings ?? 0}`,
    `- No-finding responses: ${result.responseSummary.noFindingResponses}`,
    `- Warnings: ${result.warnings.length}`,
    '',
    '## Audit tasks',
    '',
  ];
  for (const task of result.taskBundle.tasks) {
    lines.push(`### ${task.id} / ${task.claimId}`, '', `- Status: ${task.status}`, `- Candidate locations: ${task.candidateLocations.length}`, '');
    lines.push('Proof-attempt prompt:');
    lines.push(`- Map: ${task.proofAttemptPrompt.map.replace(/\n/g, ' ')}`);
    lines.push(`- Prove: ${task.proofAttemptPrompt.prove}`);
    lines.push(`- Stress-Test: ${task.proofAttemptPrompt.stressTest}`);
    lines.push(`- Report: ${task.proofAttemptPrompt.report}`);
    lines.push('');
    if (task.candidateLocations.length > 0) {
      lines.push('Candidate locations:');
      for (const location of task.candidateLocations) {
        lines.push(`- \`${lineRef(location)}\`: ${location.reason}`);
      }
      lines.push('');
    }
    if (task.warnings.length > 0) {
      lines.push('Task warnings:');
      for (const entry of task.warnings) {
        lines.push(`- \`${entry.code}\` ${entry.path}: ${entry.message}`);
      }
      lines.push('');
    }
  }
  lines.push('## Claim audit statuses', '');
  for (const outcome of result.auditOutcomes) {
    const findingSuffix = outcome.findingIds.length > 0 ? ` (${outcome.findingIds.join(', ')})` : '';
    const rationaleSuffix = outcome.rationale ? ` — ${outcome.rationale}` : '';
    lines.push(`- ${outcome.taskId} / ${outcome.claimId}: ${outcome.result}${findingSuffix}${rationaleSuffix}`);
  }
  lines.push('', '## Findings', '');
  if (!result.findings) {
    lines.push('- Dry-run mode: no `security-finding/v1` artifact was generated because no response fixture was supplied.');
  } else {
    for (const finding of result.findings.findings) {
      lines.push(`- ${finding['id']} / ${finding['claimId']}: ${finding['title']} (${finding['severity']}, candidate)`);
    }
  }
  lines.push('', '## Warnings', '');
  if (result.warnings.length === 0) {
    lines.push('- None');
  } else {
    for (const entry of result.warnings) {
      lines.push(`- \`${entry.code}\` ${entry.path}: ${entry.message}`);
    }
  }
  lines.push('');
  return lines.join('\n');
}

async function writeJson(filePath: string, value: unknown): Promise<void> {
  await fs.mkdir(path.dirname(filePath), { recursive: true });
  await fs.writeFile(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

async function writeText(filePath: string, value: string): Promise<void> {
  await fs.mkdir(path.dirname(filePath), { recursive: true });
  await fs.writeFile(filePath, value, 'utf8');
}

export async function generateSecurityProofAudit(
  claimsPath: string,
  codeMapPath: string,
  scopePath: string,
  outPath: string,
  options: SecurityAuditOptions = {},
): Promise<SecurityAuditResult> {
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const repoRoot = resolveSchemaRoot(options.repoRoot);
  const resolvedClaimsPath = path.resolve(claimsPath);
  const resolvedCodeMapPath = path.resolve(codeMapPath);
  const resolvedScopePath = path.resolve(scopePath);
  const responseFixturePath = options.responseFixture ? path.resolve(options.responseFixture) : undefined;
  const outputPaths = outputPathsFor(outPath, responseFixturePath !== undefined);

  const rawClaims = await loadJson(resolvedClaimsPath);
  const rawCodeMap = await loadJson(resolvedCodeMapPath);
  const rawScope = await loadJson(resolvedScopePath);

  if (options.validate !== false) {
    await validateWithSchema(repoRoot, 'security-claim-v1.schema.json', rawClaims, 'security-claim/v1 input');
    await validateWithSchema(repoRoot, 'security-code-map-v1.schema.json', rawCodeMap, 'security-code-map/v1 input');
    await validateWithSchema(repoRoot, 'security-audit-scope-v1.schema.json', rawScope, 'security-audit-scope/v1 input');
  }

  const claims = parseClaims(rawClaims);
  const codeMap = parseCodeMap(rawCodeMap);
  const scope = parseScope(rawScope);
  const taskBundle = buildSecurityAuditTaskBundle(claims, codeMap, scope, generatedAt, {
    origin: 'deterministic',
    generator: GENERATOR,
    claims: portablePathFrom(repoRoot, resolvedClaimsPath),
    codeMap: portablePathFrom(repoRoot, resolvedCodeMapPath),
    scope: portablePathFrom(repoRoot, resolvedScopePath),
  });

  let findings: SecurityFindingDocument | undefined;
  let responseSummary: SecurityAuditResult['responseSummary'] = {
    totalResponses: 0,
    findingResponses: 0,
    noFindingResponses: 0,
    missingResponses: taskBundle.tasks.length,
  };
  let auditOutcomes: SecurityAuditOutcome[] = taskBundle.tasks.map((task) => ({
    taskId: task.id,
    claimId: task.claimId,
    result: 'missing-response',
    findingIds: [],
  }));
  const warnings: AuditWarning[] = [...taskBundle.warnings, ...taskBundle.tasks.flatMap((task) => task.warnings)];

  if (responseFixturePath) {
    const responseFixture = parseResponseFixture(await loadJson(responseFixturePath));
    const normalized = normalizeAuditResponsesToFindings(responseFixture, taskBundle, generatedAt, {
      taskBundlePath: portablePathFrom(repoRoot, outputPaths.tasks),
      codeMapPath: portablePathFrom(repoRoot, resolvedCodeMapPath),
    });
    findings = normalized.findings;
    warnings.push(...normalized.warnings);
    responseSummary = normalized.responseSummary;
    auditOutcomes = normalized.auditOutcomes;
  }

  if (options.validate !== false) {
    await validateWithSchema(repoRoot, 'security-audit-task-bundle-v1.schema.json', taskBundle, 'security-audit-task-bundle/v1 output');
    if (findings) {
      await validateWithSchema(repoRoot, 'security-finding-v1.schema.json', findings, 'security-finding/v1 output');
    }
  }

  const result: SecurityAuditResult = {
    generatedAt,
    taskBundle,
    ...(findings !== undefined ? { findings } : {}),
    warnings,
    outputPaths,
    responseSummary,
    auditOutcomes,
  };

  await writeJson(outputPaths.tasks, taskBundle);
  if (findings && outputPaths.findings) {
    await writeJson(outputPaths.findings, findings);
  }
  await writeText(outputPaths.summaryMarkdown, renderSummaryMarkdown(result));

  return result;
}
