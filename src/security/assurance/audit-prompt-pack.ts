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
type ClaimType = 'invariant' | 'precondition' | 'postcondition' | 'assumption';
type Criticality = 'low' | 'medium' | 'high' | 'critical';
type SourceTaskStatus = 'ready' | 'blocked-no-candidate-location' | 'blocked-missing-code-map';
type PromptTaskStatus = 'ready' | 'blocked';

type CandidateLocation = {
  path: string;
  startLine: number;
  endLine: number;
  reason: string;
  symbol?: string;
  matchedTerms?: string[];
};

type SecurityClaim = {
  id: string;
  statement: string;
  type?: ClaimType;
  criticality?: Criticality;
  targetLevel?: string;
  trustBoundary?: JsonRecord;
};

type SecurityClaimDocument = {
  schemaVersion: 'security-claim/v1';
  claims: SecurityClaim[];
};

type SecurityCodeMapDocument = {
  schemaVersion: 'security-code-map/v1';
  mappings: Array<{
    claimId: string;
    candidateLocations: CandidateLocation[];
  }>;
};

type SecurityAuditTask = {
  id: string;
  claimId: string;
  claimStatement: string;
  status: SourceTaskStatus;
  candidateLocations: CandidateLocation[];
  scopeRefs: string[];
  proofAttemptPrompt?: {
    map?: string;
    prove?: string;
    stressTest?: string;
    report?: string;
  };
  warnings?: PromptWarning[];
};

type SecurityAuditTaskBundleDocument = {
  schemaVersion: 'security-audit-task-bundle/v1';
  tasks: SecurityAuditTask[];
};

export interface PromptWarning {
  code: string;
  path: string;
  message: string;
}

export interface SecurityAuditPromptPackTask {
  taskId: string;
  claimId: string;
  promptPath: string;
  status: PromptTaskStatus;
  sourceTaskStatus: SourceTaskStatus;
  claim: {
    statement: string;
    type?: ClaimType;
    criticality?: Criticality;
    targetLevel?: string;
  };
  scopeRefs: string[];
  candidateLocations: CandidateLocation[];
  warnings?: PromptWarning[];
}

export interface SecurityAuditPromptPackDocument {
  schemaVersion: 'security-audit-prompt-pack/v1';
  generatedAt: string;
  tasks: SecurityAuditPromptPackTask[];
  summary: {
    totalTasks: number;
    readyTasks: number;
    blockedTasks: number;
    totalCandidateLocations: number;
    totalWarnings: number;
  };
  provenance: {
    origin: 'deterministic';
    generator: string;
    tasks: string;
    codeMap: string;
    claims: string;
  };
  warnings?: PromptWarning[];
}

export interface SecurityAuditPromptPackOptions {
  generatedAt?: string;
  repoRoot?: string;
  validate?: boolean;
}

export interface SecurityAuditPromptPackResult {
  generatedAt: string;
  promptPack: SecurityAuditPromptPackDocument;
  warnings: PromptWarning[];
  outputPaths: {
    promptPack: string;
    summaryMarkdown: string;
    promptsDir: string;
    prompts: string[];
  };
}

const GENERATOR = 'security-audit-prompt-pack';
const MODULE_DIR = path.dirname(fileURLToPath(import.meta.url));
const CLAIM_TYPES: readonly ClaimType[] = ['invariant', 'precondition', 'postcondition', 'assumption'];
const CRITICALITIES: readonly Criticality[] = ['low', 'medium', 'high', 'critical'];
const SOURCE_TASK_STATUSES: readonly SourceTaskStatus[] = ['ready', 'blocked-no-candidate-location', 'blocked-missing-code-map'];

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

function normalizeClaimType(value: unknown): ClaimType | undefined {
  const candidate = asString(value)?.toLowerCase();
  return candidate && (CLAIM_TYPES as readonly string[]).includes(candidate) ? candidate as ClaimType : undefined;
}

function normalizeCriticality(value: unknown): Criticality | undefined {
  const candidate = asString(value)?.toLowerCase();
  return candidate && (CRITICALITIES as readonly string[]).includes(candidate) ? candidate as Criticality : undefined;
}

function normalizeSourceTaskStatus(value: unknown): SourceTaskStatus {
  const candidate = asString(value);
  return candidate && (SOURCE_TASK_STATUSES as readonly string[]).includes(candidate) ? candidate as SourceTaskStatus : 'blocked-missing-code-map';
}

function portablePathFrom(repoRoot: string, targetPath: string): string {
  return normalizeArtifactPath(targetPath, { repoRoot }) ?? targetPath.replace(/\\/g, '/');
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
    if (existsSync(path.join(candidate, 'schema/security-audit-prompt-pack-v1.schema.json'))) {
      return candidate;
    }
  }
  throw new Error('Unable to locate ae-framework schema directory for security audit prompt-pack validation.');
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

function parseCandidateLocation(rawLocation: unknown, pathRef: string): CandidateLocation {
  if (!isRecord(rawLocation)) {
    throw new Error(`Candidate location ${pathRef} must be an object.`);
  }
  const candidatePath = asString(rawLocation['path']);
  if (!candidatePath) {
    throw new Error(`Candidate location ${pathRef} must have a non-empty path.`);
  }
  const startLine = typeof rawLocation['startLine'] === 'number' ? Math.max(1, Math.floor(rawLocation['startLine'])) : 1;
  const rawEndLine = typeof rawLocation['endLine'] === 'number' ? Math.max(1, Math.floor(rawLocation['endLine'])) : startLine;
  const parsed: CandidateLocation = {
    path: candidatePath,
    startLine,
    endLine: Math.max(startLine, rawEndLine),
    reason: asString(rawLocation['reason']) ?? 'Candidate location supplied by security-code-map/v1.',
  };
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

function parseClaims(document: unknown): SecurityClaimDocument {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-claim/v1' || !Array.isArray(document['claims'])) {
    throw new Error('Expected security-claim/v1 document with a claims array.');
  }
  const seen = new Map<string, number>();
  const claims = document['claims'].map((rawClaim, index) => {
    if (!isRecord(rawClaim)) {
      throw new Error(`Security claim at index ${index} must be an object.`);
    }
    const id = asString(rawClaim['id']);
    if (!id) {
      throw new Error(`Security claim at index ${index} must have a non-empty id.`);
    }
    const duplicateIndex = seen.get(id);
    if (duplicateIndex !== undefined) {
      throw new Error(`Security claim id '${id}' at index ${index} duplicates index ${duplicateIndex}.`);
    }
    seen.set(id, index);
    const parsed: SecurityClaim = {
      id,
      statement: asString(rawClaim['statement']) ?? `Security claim ${id}`,
    };
    const claimType = normalizeClaimType(rawClaim['type']);
    if (claimType !== undefined) {
      parsed.type = claimType;
    }
    const criticality = normalizeCriticality(rawClaim['criticality']);
    if (criticality !== undefined) {
      parsed.criticality = criticality;
    }
    const targetLevel = asString(rawClaim['targetLevel']);
    if (targetLevel !== undefined) {
      parsed.targetLevel = targetLevel;
    }
    if (isRecord(rawClaim['trustBoundary'])) {
      parsed.trustBoundary = rawClaim['trustBoundary'];
    }
    return parsed;
  });
  return { schemaVersion: 'security-claim/v1', claims };
}

function parseCodeMap(document: unknown): SecurityCodeMapDocument {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-code-map/v1' || !Array.isArray(document['mappings'])) {
    throw new Error('Expected security-code-map/v1 document with a mappings array.');
  }
  const seen = new Map<string, number>();
  const mappings = document['mappings'].map((rawMapping, mappingIndex) => {
    if (!isRecord(rawMapping)) {
      throw new Error(`Security code-map mapping at index ${mappingIndex} must be an object.`);
    }
    const claimId = asString(rawMapping['claimId']);
    if (!claimId) {
      throw new Error(`Security code-map mapping at index ${mappingIndex} must have a non-empty claimId.`);
    }
    const duplicateIndex = seen.get(claimId);
    if (duplicateIndex !== undefined) {
      throw new Error(`Security code-map claimId '${claimId}' at index ${mappingIndex} duplicates index ${duplicateIndex}.`);
    }
    seen.set(claimId, mappingIndex);
    const candidateLocations = Array.isArray(rawMapping['candidateLocations'])
      ? rawMapping['candidateLocations'].map((rawLocation, locationIndex) => parseCandidateLocation(rawLocation, `/mappings/${mappingIndex}/candidateLocations/${locationIndex}`))
      : [];
    return { claimId, candidateLocations };
  });
  return { schemaVersion: 'security-code-map/v1', mappings };
}

function parseTaskBundle(document: unknown): SecurityAuditTaskBundleDocument {
  if (!isRecord(document) || document['schemaVersion'] !== 'security-audit-task-bundle/v1' || !Array.isArray(document['tasks'])) {
    throw new Error('Expected security-audit-task-bundle/v1 document with a tasks array.');
  }
  const seen = new Map<string, number>();
  const tasks = document['tasks'].map((rawTask, taskIndex) => {
    if (!isRecord(rawTask)) {
      throw new Error(`Security audit task at index ${taskIndex} must be an object.`);
    }
    const id = asString(rawTask['id']);
    const claimId = asString(rawTask['claimId']);
    if (!id || !claimId) {
      throw new Error(`Security audit task at index ${taskIndex} must have non-empty id and claimId.`);
    }
    const duplicateIndex = seen.get(id);
    if (duplicateIndex !== undefined) {
      throw new Error(`Security audit task id '${id}' at index ${taskIndex} duplicates index ${duplicateIndex}.`);
    }
    seen.set(id, taskIndex);
    const proofAttemptPrompt: SecurityAuditTask['proofAttemptPrompt'] | undefined = isRecord(rawTask['proofAttemptPrompt'])
      ? {}
      : undefined;
    if (proofAttemptPrompt !== undefined && isRecord(rawTask['proofAttemptPrompt'])) {
      const map = asString(rawTask['proofAttemptPrompt']['map']);
      if (map !== undefined) {
        proofAttemptPrompt.map = map;
      }
      const prove = asString(rawTask['proofAttemptPrompt']['prove']);
      if (prove !== undefined) {
        proofAttemptPrompt.prove = prove;
      }
      const stressTest = asString(rawTask['proofAttemptPrompt']['stressTest']);
      if (stressTest !== undefined) {
        proofAttemptPrompt.stressTest = stressTest;
      }
      const report = asString(rawTask['proofAttemptPrompt']['report']);
      if (report !== undefined) {
        proofAttemptPrompt.report = report;
      }
    }
    const warnings = Array.isArray(rawTask['warnings'])
      ? rawTask['warnings'].filter(isRecord).map((entry, warningIndex) => ({
          code: asString(entry['code']) ?? 'task-warning',
          path: asString(entry['path']) ?? `/tasks/${taskIndex}/warnings/${warningIndex}`,
          message: asString(entry['message']) ?? 'Security audit task warning.',
        }))
      : [];
    const parsed: SecurityAuditTask = {
      id,
      claimId,
      claimStatement: asString(rawTask['claimStatement']) ?? `Security claim ${claimId}`,
      status: normalizeSourceTaskStatus(rawTask['status']),
      candidateLocations: Array.isArray(rawTask['candidateLocations'])
        ? rawTask['candidateLocations'].map((rawLocation, locationIndex) => parseCandidateLocation(rawLocation, `/tasks/${taskIndex}/candidateLocations/${locationIndex}`))
        : [],
      scopeRefs: unique(asStringArray(rawTask['scopeRefs'])),
    };
    if (proofAttemptPrompt !== undefined) {
      parsed.proofAttemptPrompt = proofAttemptPrompt;
    }
    if (warnings.length > 0) {
      parsed.warnings = warnings;
    }
    return parsed;
  });
  return { schemaVersion: 'security-audit-task-bundle/v1', tasks };
}

function fileNameForTask(taskId: string, index: number, used: Set<string>): string {
  const candidate = taskId.replace(/[^A-Za-z0-9._-]/g, '-').replace(/-+/g, '-').replace(/^-|-$/g, '') || `task-${index + 1}`;
  let fileName = `${candidate}.md`;
  let suffix = 2;
  while (used.has(fileName)) {
    fileName = `${candidate}-${suffix}.md`;
    suffix += 1;
  }
  used.add(fileName);
  return fileName;
}

function lineRef(location: CandidateLocation): string {
  const symbol = location.symbol ? ` (${location.symbol})` : '';
  return `${location.path}:${location.startLine}-${location.endLine}${symbol}`;
}

function trustBoundarySummary(claim?: SecurityClaim): string[] {
  if (!claim?.trustBoundary) {
    return ['n/a'];
  }
  const entries: string[] = [];
  const boundaryIds = unique([...asStringArray(claim.trustBoundary['boundaryIds']), ...asStringArray(claim.trustBoundary['id'])]);
  if (boundaryIds.length > 0) {
    entries.push(`Boundary IDs: ${boundaryIds.join(', ')}`);
  }
  const entryPoints = unique(asStringArray(claim.trustBoundary['entryPoints']));
  if (entryPoints.length > 0) {
    entries.push(`Entry points: ${entryPoints.join(', ')}`);
  }
  const dataClasses = unique(asStringArray(claim.trustBoundary['dataClasses']));
  if (dataClasses.length > 0) {
    entries.push(`Data classes: ${dataClasses.join(', ')}`);
  }
  if (typeof claim.trustBoundary['attackerControlled'] === 'boolean') {
    entries.push(`Attacker controlled: ${claim.trustBoundary['attackerControlled'] ? 'yes' : 'no'}`);
  }
  return entries.length > 0 ? entries : ['n/a'];
}

function renderNestedList(values: string[]): string {
  return values.length > 0 ? values.map((entry) => `  - ${entry}`).join('\n') : '  - n/a';
}

function renderCandidateLocations(locations: CandidateLocation[]): string {
  if (locations.length === 0) {
    return '  - No candidate source location was resolved. Treat this prompt as blocked until code-map evidence is provided.';
  }
  return locations.map((location) => `  - ${lineRef(location)}: ${location.reason}`).join('\n');
}

function renderPrompt(task: SecurityAuditPromptPackTask, sourceTask?: SecurityAuditTask, sourceClaim?: SecurityClaim): string {
  const prompt = sourceTask?.proofAttemptPrompt;
  const lines = [
    '# Security proof-attempt audit task',
    '',
    '## Claim',
    '',
    `- Claim ID: ${task.claimId}`,
    `- Statement: ${task.claim.statement}`,
    `- Type: ${task.claim.type ?? 'n/a'}`,
    `- Criticality: ${task.claim.criticality ?? 'n/a'}`,
    `- Target assurance level: ${task.claim.targetLevel ?? 'n/a'}`,
    '',
    '## Scope and trust boundary',
    '',
    '- Scope refs:',
    renderNestedList(task.scopeRefs),
    '- Attacker-controlled assumptions:',
    renderNestedList(trustBoundarySummary(sourceClaim)),
    '- Candidate source locations:',
    renderCandidateLocations(task.candidateLocations),
    '',
    '## Instructions',
    '',
    'You are reviewing this repository under the authorized security audit scope.',
    '',
    'Do not treat any result as a confirmed vulnerability.',
    'Report only candidate findings.',
    'Do not generate exploit automation or weaponized PoC.',
    'Use proof-attempt reasoning:',
    '',
    '1. Map:',
    '   Identify the relevant code paths.',
    prompt?.map ? `   Source task hint: ${prompt.map.replace(/\r?\n/g, ' ')}` : '',
    '',
    '2. Prove:',
    '   Try to prove that the implementation satisfies the security claim.',
    prompt?.prove ? `   Source task hint: ${prompt.prove}` : '',
    '',
    '3. Stress-Test:',
    '   Look for attacker-controlled inputs, edge cases, and trust-boundary assumptions that could break the proof.',
    prompt?.stressTest ? `   Source task hint: ${prompt.stressTest}` : '',
    '',
    '4. Report:',
    '   Only report a candidate finding if the proof fails with concrete code evidence.',
    prompt?.report ? `   Source task hint: ${prompt.report}` : '',
    '',
    '## Expected output',
    '',
    'Return JSON compatible with a security-audit-response-fixture/v1 response item.',
    'Use `result: "finding"` only for candidate findings with concrete code evidence.',
    'Use `result: "no-finding"` when the proof succeeds or evidence is insufficient.',
    'For `no-finding`, omit the `finding` object and keep the rationale explicit.',
    'Never emit a confirmed vulnerability from this prompt pack.',
    '',
    '```json',
    JSON.stringify({
      taskId: task.taskId,
      claimId: task.claimId,
      result: 'finding',
      finding: {
        status: 'candidate',
        severity: task.claim.criticality ?? 'medium',
        title: '<candidate finding title>',
        summary: '<why the proof failed with concrete code evidence>',
        affectedLocations: task.candidateLocations.map((location) => ({
          path: location.path,
          startLine: location.startLine,
          endLine: location.endLine,
          ...(location.symbol !== undefined ? { symbol: location.symbol } : {}),
        })),
      },
      rationale: '<short proof-attempt rationale>',
    }, null, 2),
    '```',
    '',
  ];
  return `${lines.join('\n')}\n`;
}

function outputPathsFor(outPath: string): { promptPack: string; summaryMarkdown: string; promptsDir: string } {
  const resolvedOut = path.resolve(outPath);
  if (path.extname(resolvedOut).toLowerCase() === '.json') {
    const baseDir = path.dirname(resolvedOut);
    return {
      promptPack: resolvedOut,
      summaryMarkdown: path.join(baseDir, 'security-audit-prompt-summary.md'),
      promptsDir: path.join(baseDir, 'prompts'),
    };
  }
  return {
    promptPack: path.join(resolvedOut, 'security-audit-prompt-pack.json'),
    summaryMarkdown: path.join(resolvedOut, 'security-audit-prompt-summary.md'),
    promptsDir: path.join(resolvedOut, 'prompts'),
  };
}

function buildPromptTask(params: {
  task: SecurityAuditTask;
  taskIndex: number;
  claim: SecurityClaim | undefined;
  codeMapLocations: CandidateLocation[];
  promptPath: string;
  repoRoot: string;
}): SecurityAuditPromptPackTask {
  const candidateLocations = params.task.candidateLocations.length > 0 ? params.task.candidateLocations : params.codeMapLocations;
  const warnings: PromptWarning[] = [...(params.task.warnings ?? [])];
  if (!params.claim) {
    warnings.push({
      code: 'missing-claim-metadata',
      path: `/tasks/${params.taskIndex}/claim`,
      message: `No security-claim/v1 metadata was found for ${params.task.claimId}.`,
    });
  }
  if (candidateLocations.length === 0) {
    warnings.push({
      code: 'missing-candidate-location',
      path: `/tasks/${params.taskIndex}/candidateLocations`,
      message: `No candidate source location was found for ${params.task.claimId}.`,
    });
  }
  const claimSummary: SecurityAuditPromptPackTask['claim'] = {
    statement: params.claim?.statement ?? params.task.claimStatement,
  };
  if (params.claim?.type !== undefined) {
    claimSummary.type = params.claim.type;
  }
  if (params.claim?.criticality !== undefined) {
    claimSummary.criticality = params.claim.criticality;
  }
  if (params.claim?.targetLevel !== undefined) {
    claimSummary.targetLevel = params.claim.targetLevel;
  }
  const promptTask: SecurityAuditPromptPackTask = {
    taskId: params.task.id,
    claimId: params.task.claimId,
    promptPath: portablePathFrom(params.repoRoot, params.promptPath),
    status: params.task.status === 'ready' && candidateLocations.length > 0 ? 'ready' : 'blocked',
    sourceTaskStatus: params.task.status,
    claim: claimSummary,
    scopeRefs: params.task.scopeRefs.length > 0 ? params.task.scopeRefs : ['security-audit-scope'],
    candidateLocations,
  };
  if (warnings.length > 0) {
    promptTask.warnings = warnings;
  }
  return promptTask;
}

function summarizePromptTasks(tasks: SecurityAuditPromptPackTask[], warnings: PromptWarning[]): SecurityAuditPromptPackDocument['summary'] {
  const taskWarnings = tasks.reduce((count, task) => count + (task.warnings?.length ?? 0), 0);
  return {
    totalTasks: tasks.length,
    readyTasks: tasks.filter((task) => task.status === 'ready').length,
    blockedTasks: tasks.filter((task) => task.status === 'blocked').length,
    totalCandidateLocations: tasks.reduce((count, task) => count + task.candidateLocations.length, 0),
    totalWarnings: warnings.length + taskWarnings,
  };
}

function renderSummaryMarkdown(result: SecurityAuditPromptPackResult): string {
  const lines = [
    '# Security audit prompt pack summary',
    '',
    `- Generated at: ${result.generatedAt}`,
    `- Prompt pack: ${portablePathFrom(process.cwd(), result.outputPaths.promptPack)}`,
    `- Prompts: ${result.promptPack.summary.totalTasks}`,
    `- Ready tasks: ${result.promptPack.summary.readyTasks}`,
    `- Blocked tasks: ${result.promptPack.summary.blockedTasks}`,
    `- Candidate locations: ${result.promptPack.summary.totalCandidateLocations}`,
    `- Warnings: ${result.promptPack.summary.totalWarnings}`,
    '',
    '## Tasks',
    '',
  ];
  for (const task of result.promptPack.tasks) {
    lines.push(`### ${task.taskId} / ${task.claimId}`, '');
    lines.push(`- Status: ${task.status} (source: ${task.sourceTaskStatus})`);
    lines.push(`- Prompt: ${task.promptPath}`);
    lines.push(`- Claim type: ${task.claim.type ?? 'n/a'}`);
    lines.push(`- Criticality: ${task.claim.criticality ?? 'n/a'}`);
    lines.push(`- Target assurance level: ${task.claim.targetLevel ?? 'n/a'}`);
    lines.push(`- Candidate locations: ${task.candidateLocations.length}`);
    if (task.warnings && task.warnings.length > 0) {
      lines.push('- Warnings:');
      for (const warning of task.warnings) {
        lines.push(`  - ${warning.code}: ${warning.message}`);
      }
    }
    lines.push('');
  }
  lines.push('## Pack warnings', '');
  if (result.warnings.length === 0) {
    lines.push('- None');
  } else {
    for (const warning of result.warnings) {
      lines.push(`- ${warning.code} ${warning.path}: ${warning.message}`);
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

export function buildSecurityAuditPromptPack(
  taskBundle: SecurityAuditTaskBundleDocument,
  codeMap: SecurityCodeMapDocument,
  claims: SecurityClaimDocument,
  generatedAt: string,
  outputPaths: { promptsDir: string },
  repoRoot: string,
  provenance: SecurityAuditPromptPackDocument['provenance'],
): { promptPack: SecurityAuditPromptPackDocument; promptMarkdownByPath: Map<string, string>; warnings: PromptWarning[] } {
  const warnings: PromptWarning[] = [];
  const claimsById = new Map(claims.claims.map((claim) => [claim.id, claim]));
  const codeMapByClaim = new Map(codeMap.mappings.map((mapping) => [mapping.claimId, mapping]));
  const usedPromptFileNames = new Set<string>();
  const promptMarkdownByPath = new Map<string, string>();
  const tasks = taskBundle.tasks.map((task, taskIndex) => {
    const promptPath = path.join(outputPaths.promptsDir, fileNameForTask(task.id, taskIndex, usedPromptFileNames));
    const promptTask = buildPromptTask({
      task,
      taskIndex,
      claim: claimsById.get(task.claimId),
      codeMapLocations: codeMapByClaim.get(task.claimId)?.candidateLocations ?? [],
      promptPath,
      repoRoot,
    });
    promptMarkdownByPath.set(promptPath, renderPrompt(promptTask, task, claimsById.get(task.claimId)));
    return promptTask;
  });
  const promptPack: SecurityAuditPromptPackDocument = {
    schemaVersion: 'security-audit-prompt-pack/v1',
    generatedAt,
    tasks,
    summary: summarizePromptTasks(tasks, warnings),
    provenance,
  };
  if (warnings.length > 0) {
    promptPack.warnings = warnings;
  }
  return { promptPack, promptMarkdownByPath, warnings };
}

export async function generateSecurityAuditPromptPack(
  tasksPath: string,
  codeMapPath: string,
  claimsPath: string,
  outPath: string,
  options: SecurityAuditPromptPackOptions = {},
): Promise<SecurityAuditPromptPackResult> {
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const repoRoot = resolveSchemaRoot(options.repoRoot);
  const resolvedTasksPath = path.resolve(tasksPath);
  const resolvedCodeMapPath = path.resolve(codeMapPath);
  const resolvedClaimsPath = path.resolve(claimsPath);
  const outputPaths = outputPathsFor(outPath);

  const rawTasks = await loadJson(resolvedTasksPath);
  const rawCodeMap = await loadJson(resolvedCodeMapPath);
  const rawClaims = await loadJson(resolvedClaimsPath);

  if (options.validate !== false) {
    await validateWithSchema(repoRoot, 'security-audit-task-bundle-v1.schema.json', rawTasks, 'security-audit-task-bundle/v1 input');
    await validateWithSchema(repoRoot, 'security-code-map-v1.schema.json', rawCodeMap, 'security-code-map/v1 input');
    await validateWithSchema(repoRoot, 'security-claim-v1.schema.json', rawClaims, 'security-claim/v1 input');
  }

  const taskBundle = parseTaskBundle(rawTasks);
  const codeMap = parseCodeMap(rawCodeMap);
  const claims = parseClaims(rawClaims);
  const built = buildSecurityAuditPromptPack(taskBundle, codeMap, claims, generatedAt, outputPaths, repoRoot, {
    origin: 'deterministic',
    generator: GENERATOR,
    tasks: portablePathFrom(repoRoot, resolvedTasksPath),
    codeMap: portablePathFrom(repoRoot, resolvedCodeMapPath),
    claims: portablePathFrom(repoRoot, resolvedClaimsPath),
  });

  if (options.validate !== false) {
    await validateWithSchema(repoRoot, 'security-audit-prompt-pack-v1.schema.json', built.promptPack, 'security-audit-prompt-pack/v1 output');
  }

  await writeJson(outputPaths.promptPack, built.promptPack);
  for (const [promptPath, markdown] of built.promptMarkdownByPath.entries()) {
    await writeText(promptPath, markdown);
  }
  const result: SecurityAuditPromptPackResult = {
    generatedAt,
    promptPack: built.promptPack,
    warnings: built.warnings,
    outputPaths: {
      ...outputPaths,
      prompts: [...built.promptMarkdownByPath.keys()],
    },
  };
  await writeText(outputPaths.summaryMarkdown, renderSummaryMarkdown(result));
  return result;
}
