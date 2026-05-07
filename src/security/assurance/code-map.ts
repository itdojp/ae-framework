import { existsSync, promises as fs } from 'node:fs';
import { createRequire } from 'node:module';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { glob } from 'glob';
import { normalizeArtifactPath } from '../../utils/path-normalization.js';

const require = createRequire(import.meta.url);
const Ajv2020 = require('ajv/dist/2020.js') as new (options?: JsonRecord) => {
  compile: (schema: unknown) => ((data: unknown) => boolean) & { errors?: unknown };
};
const addFormats = require('ajv-formats') as (ajv: unknown) => void;

type JsonRecord = Record<string, unknown>;
type Coverage = 'none' | 'partial' | 'full';

type SecurityClaim = {
  id: string;
  statement?: string;
  sourceRefs?: Array<Record<string, unknown>>;
  threatTags?: Record<string, unknown>;
  trustBoundary?: Record<string, unknown>;
  requiredLanes?: string[];
};

type SecurityClaimDocument = {
  schemaVersion: 'security-claim/v1';
  generatedAt?: string;
  claims: SecurityClaim[];
};

type SecurityAuditScopeDocument = {
  schemaVersion: 'security-audit-scope/v1';
  generatedAt?: string;
  inScope: string[];
  outOfScope: string[];
  trustBoundaries?: Array<Record<string, unknown>>;
};

export interface CodeMapOptions {
  generatedAt?: string;
  repoRoot?: string;
  validate?: boolean;
}

export interface CodeMapWarning {
  code: string;
  source?: string;
  path: string;
  message: string;
}

export interface CodeMapOutputPaths {
  codeMap: string;
  summaryMarkdown: string;
}

export interface CandidateLocation {
  path: string;
  startLine: number;
  endLine: number;
  symbol?: string;
  reason: string;
  matchedTerms?: string[];
}

export interface ClaimCodeMapping {
  claimId: string;
  candidateLocations: CandidateLocation[];
  coverage: Coverage;
  warnings: CodeMapWarning[];
}

export interface SecurityCodeMapDocument {
  schemaVersion: 'security-code-map/v1';
  generatedAt: string;
  mappings: ClaimCodeMapping[];
  summary: {
    totalClaims: number;
    mappedClaims: number;
    totalCandidateLocations: number;
    totalWarnings: number;
    byCoverage: Record<Coverage, number>;
  };
  provenance: {
    origin: 'deterministic';
    generator: string;
    claims: string;
    scope: string;
    target: string;
  };
  warnings: CodeMapWarning[];
}

export interface CodeMapResult {
  generatedAt: string;
  codeMap: SecurityCodeMapDocument;
  warnings: CodeMapWarning[];
  outputPaths: CodeMapOutputPaths;
}

type SourceSymbol = {
  name: string;
  startLine: number;
  endLine: number;
  text: string;
};

type SourceFile = {
  absolutePath: string;
  repoRelativePath: string;
  targetRelativePath: string;
  text: string;
  lines: string[];
  symbols: SourceSymbol[];
};

const GENERATOR = 'security-code-map-producer';
const MODULE_DIR = path.dirname(fileURLToPath(import.meta.url));
const SOURCE_EXTENSIONS = new Set(['.ts', '.tsx', '.js', '.jsx', '.mjs', '.cjs']);
const DEFAULT_IGNORES = ['node_modules/**', '.git/**', 'dist/**', 'coverage/**', 'artifacts/**'];
const MAX_CANDIDATES_PER_CLAIM = 5;
const STOP_WORDS = new Set([
  'the',
  'and',
  'that',
  'must',
  'with',
  'from',
  'into',
  'this',
  'have',
  'has',
  'all',
  'for',
  'are',
  'affect',
  'affects',
  'result',
  'results',
  'include',
  'includes',
  'including',
]);

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
    if (existsSync(path.join(candidate, 'schema/security-code-map-v1.schema.json'))) {
      return candidate;
    }
  }
  throw new Error('Unable to locate ae-framework schema directory for security code-map validation.');
}

function outputPathsFor(outPath: string): CodeMapOutputPaths {
  const resolvedOut = path.resolve(outPath);
  if (path.extname(resolvedOut).toLowerCase() === '.json') {
    return {
      codeMap: resolvedOut,
      summaryMarkdown: resolvedOut.replace(/\.json$/i, '.md'),
    };
  }
  return {
    codeMap: path.join(resolvedOut, 'security-code-map.json'),
    summaryMarkdown: path.join(resolvedOut, 'security-code-map.md'),
  };
}

function warning(code: string, pathRef: string, message: string, source?: string): CodeMapWarning {
  return {
    code,
    ...(source !== undefined ? { source } : {}),
    path: pathRef,
    message,
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
  const claims = document['claims'].map((claim, index) => {
    if (!isRecord(claim)) {
      throw new Error(`Security claim at index ${index} must be an object.`);
    }
    const id = asString(claim['id']);
    if (!id) {
      throw new Error(`Security claim at index ${index} must have a non-empty id.`);
    }
    const parsed: SecurityClaim = { id };
    const statement = asString(claim['statement']);
    if (statement !== undefined) {
      parsed.statement = statement;
    }
    if (Array.isArray(claim['sourceRefs'])) {
      parsed.sourceRefs = claim['sourceRefs'].filter(isRecord);
    }
    if (isRecord(claim['threatTags'])) {
      parsed.threatTags = claim['threatTags'];
    }
    if (isRecord(claim['trustBoundary'])) {
      parsed.trustBoundary = claim['trustBoundary'];
    }
    if (Array.isArray(claim['requiredLanes'])) {
      parsed.requiredLanes = asStringArray(claim['requiredLanes']);
    }
    return parsed;
  });
  const parsedDocument: SecurityClaimDocument = {
    schemaVersion: 'security-claim/v1',
    claims,
  };
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
  const inScope = asStringArray(document['inScope']);
  if (inScope.length === 0) {
    throw new Error('Security audit scope must include at least one inScope glob.');
  }
  const parsedScope: SecurityAuditScopeDocument = {
    schemaVersion: 'security-audit-scope/v1',
    inScope: [...new Set(inScope)],
    outOfScope: [...new Set(asStringArray(document['outOfScope']))],
  };
  const generatedAt = asString(document['generatedAt']);
  if (generatedAt !== undefined) {
    parsedScope.generatedAt = generatedAt;
  }
  if (Array.isArray(document['trustBoundaries'])) {
    parsedScope.trustBoundaries = document['trustBoundaries'].filter(isRecord);
  }
  return parsedScope;
}

function normalizePattern(pattern: string): string {
  return pattern.replace(/\\/g, '/').replace(/^\.\//, '');
}

function isUnsafeGlobPattern(pattern: string): boolean {
  const normalized = normalizePattern(pattern);
  return path.isAbsolute(pattern) || normalized === '..' || normalized.startsWith('../') || normalized.includes('/../') || normalized.endsWith('/..');
}

function pushDocumentWarning(warnings: CodeMapWarning[], code: string, message: string, source?: string): void {
  warnings.push(warning(code, `/warnings/${warnings.length}`, message, source));
}

function safeScopePatterns(patterns: string[], kind: 'inScope' | 'outOfScope', warnings: CodeMapWarning[]): string[] {
  const safePatterns: string[] = [];
  for (const [index, pattern] of patterns.entries()) {
    if (isUnsafeGlobPattern(pattern)) {
      warnings.push(warning(
        'unsafe-glob-pattern',
        `/scope/${kind}/${index}`,
        `Ignored ${kind} glob '${pattern}' because it escapes the target root.`,
      ));
      continue;
    }
    safePatterns.push(normalizePattern(pattern));
  }
  return safePatterns;
}

function isInsideDirectory(parentDir: string, candidatePath: string): boolean {
  const relative = path.relative(parentDir, candidatePath);
  return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
}

function isSupportedSource(filePath: string): boolean {
  if (filePath.endsWith('.d.ts')) {
    return false;
  }
  return SOURCE_EXTENSIONS.has(path.extname(filePath).toLowerCase());
}

async function collectFiles(targetRoot: string, scope: SecurityAuditScopeDocument, repoRoot: string, warnings: CodeMapWarning[]): Promise<SourceFile[]> {
  const resolvedTargetRoot = path.resolve(targetRoot);
  const inScope = safeScopePatterns(scope.inScope, 'inScope', warnings);
  const ignore = [...DEFAULT_IGNORES, ...safeScopePatterns(scope.outOfScope, 'outOfScope', warnings)];
  const matches = new Set<string>();
  for (const pattern of inScope) {
    const found = await glob(pattern, {
      cwd: resolvedTargetRoot,
      nodir: true,
      ignore,
      windowsPathsNoEscape: true,
    });
    for (const entry of found) {
      const normalizedEntry = normalizePattern(entry);
      const absolutePath = path.resolve(resolvedTargetRoot, normalizedEntry);
      if (!isInsideDirectory(resolvedTargetRoot, absolutePath)) {
        pushDocumentWarning(
          warnings,
          'target-escape-blocked',
          `Ignored matched source '${entry}' because it resolves outside the target root.`,
        );
        continue;
      }
      if (isSupportedSource(normalizedEntry)) {
        matches.add(normalizedEntry);
      }
    }
  }

  const files: SourceFile[] = [];
  for (const targetRelativePath of [...matches].sort()) {
    const absolutePath = path.join(resolvedTargetRoot, targetRelativePath);
    const text = await fs.readFile(absolutePath, 'utf8');
    const lines = text.split(/\r?\n/);
    files.push({
      absolutePath,
      repoRelativePath: portablePathFrom(repoRoot, absolutePath),
      targetRelativePath,
      text,
      lines,
      symbols: extractSymbols(lines),
    });
  }

  if (files.length === 0) {
    pushDocumentWarning(warnings, 'no-source-files', `No supported source files matched inScope globs under ${portablePathFrom(repoRoot, resolvedTargetRoot)}.`);
  }
  return files;
}

function extractSymbols(lines: string[]): SourceSymbol[] {
  const symbols: Array<{ name: string; startLine: number }> = [];
  const symbolPattern = /^(?:export\s+)?(?:async\s+)?(?:function|class|const|let|var)\s+([A-Za-z_$][\w$]*)/;
  for (let index = 0; index < lines.length; index += 1) {
    const match = lines[index]?.match(symbolPattern);
    if (match?.[1]) {
      symbols.push({ name: match[1], startLine: index + 1 });
    }
  }
  return symbols.map((symbol, index) => {
    const next = symbols[index + 1];
    const endLine = next ? next.startLine - 1 : Math.max(symbol.startLine, lines.length);
    return {
      name: symbol.name,
      startLine: symbol.startLine,
      endLine,
      text: lines.slice(symbol.startLine - 1, endLine).join('\n'),
    };
  });
}

function tokenize(value: string): string[] {
  return value
    .toLowerCase()
    .replace(/([a-z])([A-Z])/g, '$1 $2')
    .split(/[^a-z0-9]+/)
    .map((term) => term.trim())
    .filter((term) => term.length >= 3 && !STOP_WORDS.has(term));
}

function keywordsForClaim(claim: SecurityClaim): string[] {
  const values: string[] = [];
  if (claim.statement) {
    values.push(claim.statement);
  }
  for (const ref of claim.sourceRefs ?? []) {
    values.push(...asStringArray(ref['section']));
    values.push(...asStringArray(ref['description']));
    values.push(...asStringArray(ref['uri']));
  }
  if (claim.threatTags) {
    values.push(...asStringArray(claim.threatTags['stride']));
    values.push(...asStringArray(claim.threatTags['cwe']));
  }
  if (claim.trustBoundary) {
    values.push(...asStringArray(claim.trustBoundary['entryPoints']));
    values.push(...asStringArray(claim.trustBoundary['boundaryIds']));
    values.push(...asStringArray(claim.trustBoundary['dataClasses']));
  }
  values.push(...(claim.requiredLanes ?? []));
  return [...new Set(values.flatMap(tokenize))].sort();
}

function matchedTerms(text: string, terms: string[]): string[] {
  const normalized = text.toLowerCase();
  return terms.filter((term) => normalized.includes(term));
}

function reasonFor(symbol: string | undefined, terms: string[]): string {
  const shown = terms.slice(0, 8).join(', ');
  const target = symbol ?? 'file';
  return `Matched security claim terms in ${target}: ${shown}.`;
}

function candidateForSymbol(file: SourceFile, symbol: SourceSymbol, terms: string[]): CandidateLocation | undefined {
  const matches = matchedTerms(`${symbol.name}\n${symbol.text}`, terms);
  if (matches.length === 0) {
    return undefined;
  }
  return {
    path: file.targetRelativePath,
    startLine: symbol.startLine,
    endLine: symbol.endLine,
    symbol: symbol.name,
    reason: reasonFor(symbol.name, matches),
    matchedTerms: matches,
  };
}

function candidateForFile(file: SourceFile, terms: string[]): CandidateLocation | undefined {
  const matches = matchedTerms(`${file.targetRelativePath}\n${file.text}`, terms);
  if (matches.length === 0) {
    return undefined;
  }
  return {
    path: file.targetRelativePath,
    startLine: 1,
    endLine: Math.max(1, file.lines.length),
    reason: reasonFor(undefined, matches),
    matchedTerms: matches,
  };
}

function scoreCandidate(candidate: CandidateLocation): number {
  const matchedCount = candidate.matchedTerms?.length ?? 0;
  return matchedCount * 1000 - candidate.startLine;
}

function compareStableString(left: string, right: string): number {
  if (left < right) {
    return -1;
  }
  if (left > right) {
    return 1;
  }
  return 0;
}

function mapClaim(claim: SecurityClaim, claimIndex: number, files: SourceFile[]): ClaimCodeMapping {
  const terms = keywordsForClaim(claim);
  const candidates: CandidateLocation[] = [];
  for (const file of files) {
    const symbolCandidates = file.symbols
      .map((symbol) => candidateForSymbol(file, symbol, terms))
      .filter((entry): entry is CandidateLocation => Boolean(entry));
    if (symbolCandidates.length > 0) {
      candidates.push(...symbolCandidates);
      continue;
    }
    const fileCandidate = candidateForFile(file, terms);
    if (fileCandidate) {
      candidates.push(fileCandidate);
    }
  }

  const candidateLocations = candidates
    .sort((left, right) => scoreCandidate(right) - scoreCandidate(left) || compareStableString(left.path, right.path) || left.startLine - right.startLine)
    .slice(0, MAX_CANDIDATES_PER_CLAIM);
  const warnings = candidateLocations.length === 0
    ? [warning('no-candidate-location', `/mappings/${claimIndex}/candidateLocations`, `No candidate source location was found for ${claim.id}.`)]
    : [];
  return {
    claimId: claim.id,
    candidateLocations,
    coverage: candidateLocations.length === 0 ? 'none' : 'partial',
    warnings,
  };
}

function summarize(mappings: ClaimCodeMapping[], documentWarnings: CodeMapWarning[]): SecurityCodeMapDocument['summary'] {
  const byCoverage: Record<Coverage, number> = { none: 0, partial: 0, full: 0 };
  let totalCandidateLocations = 0;
  let mappingWarnings = 0;
  for (const mapping of mappings) {
    byCoverage[mapping.coverage] += 1;
    totalCandidateLocations += mapping.candidateLocations.length;
    mappingWarnings += mapping.warnings.length;
  }
  return {
    totalClaims: mappings.length,
    mappedClaims: mappings.filter((mapping) => mapping.candidateLocations.length > 0).length,
    totalCandidateLocations,
    totalWarnings: documentWarnings.length + mappingWarnings,
    byCoverage,
  };
}

function buildDocument(
  claims: SecurityClaimDocument,
  files: SourceFile[],
  generatedAt: string,
  claimsPath: string,
  scopePath: string,
  targetRoot: string,
  repoRoot: string,
  documentWarnings: CodeMapWarning[],
): SecurityCodeMapDocument {
  const mappings = claims.claims.map((claim, index) => mapClaim(claim, index, files));
  return {
    schemaVersion: 'security-code-map/v1',
    generatedAt,
    mappings,
    summary: summarize(mappings, documentWarnings),
    provenance: {
      origin: 'deterministic',
      generator: GENERATOR,
      claims: portablePathFrom(repoRoot, claimsPath),
      scope: portablePathFrom(repoRoot, scopePath),
      target: portablePathFrom(repoRoot, targetRoot),
    },
    warnings: documentWarnings,
  };
}

function renderSummaryMarkdown(document: SecurityCodeMapDocument): string {
  const lines = [
    '# Security code-map summary',
    '',
    `- Generated at: ${document.generatedAt}`,
    `- Claims: ${document.summary.totalClaims}`,
    `- Mapped claims: ${document.summary.mappedClaims}`,
    `- Candidate locations: ${document.summary.totalCandidateLocations}`,
    `- Warnings: ${document.summary.totalWarnings}`,
    '',
    '## Mappings',
    '',
  ];
  for (const mapping of document.mappings) {
    lines.push(`### ${mapping.claimId}`, '', `- Coverage: ${mapping.coverage}`, `- Candidate locations: ${mapping.candidateLocations.length}`, '');
    if (mapping.candidateLocations.length === 0) {
      lines.push('- No candidate locations found.', '');
    } else {
      for (const location of mapping.candidateLocations) {
        const symbol = location.symbol ? ` (${location.symbol})` : '';
        lines.push(`- \`${location.path}:${location.startLine}-${location.endLine}\`${symbol}: ${location.reason}`);
      }
      lines.push('');
    }
    if (mapping.warnings.length > 0) {
      lines.push('Warnings:');
      for (const entry of mapping.warnings) {
        lines.push(`- \`${entry.code}\` ${entry.path}: ${entry.message}`);
      }
      lines.push('');
    }
  }
  lines.push('## Document warnings', '');
  if (document.warnings.length === 0) {
    lines.push('- None');
  } else {
    for (const entry of document.warnings) {
      lines.push(`- \`${entry.code}\` ${entry.path}: ${entry.message}`);
    }
  }
  lines.push('');
  return lines.join('\n');
}

async function writeJson(filePath: string, value: unknown): Promise<void> {
  await fs.writeFile(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

export async function generateSecurityCodeMap(claimsPath: string, scopePath: string, targetPath: string, outPath: string, options: CodeMapOptions = {}): Promise<CodeMapResult> {
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const repoRoot = resolveSchemaRoot(options.repoRoot);
  const resolvedClaimsPath = path.resolve(claimsPath);
  const resolvedScopePath = path.resolve(scopePath);
  const resolvedTargetPath = path.resolve(targetPath);
  const warnings: CodeMapWarning[] = [];

  const rawClaims = await loadJson(resolvedClaimsPath);
  const rawScope = await loadJson(resolvedScopePath);
  if (options.validate !== false) {
    await validateWithSchema(repoRoot, 'security-claim-v1.schema.json', rawClaims, 'Input security claims');
    await validateWithSchema(repoRoot, 'security-audit-scope-v1.schema.json', rawScope, 'Input security audit scope');
  }
  const claims = parseClaims(rawClaims);
  const scope = parseScope(rawScope);
  const files = await collectFiles(resolvedTargetPath, scope, repoRoot, warnings);
  const codeMap = buildDocument(claims, files, generatedAt, resolvedClaimsPath, resolvedScopePath, resolvedTargetPath, repoRoot, warnings);
  if (options.validate !== false) {
    await validateWithSchema(repoRoot, 'security-code-map-v1.schema.json', codeMap, 'Generated security code map');
  }

  const outputPaths = outputPathsFor(outPath);
  await fs.mkdir(path.dirname(outputPaths.codeMap), { recursive: true });
  await writeJson(outputPaths.codeMap, codeMap);
  await fs.writeFile(outputPaths.summaryMarkdown, renderSummaryMarkdown(codeMap), 'utf8');

  return {
    generatedAt,
    codeMap,
    warnings: [...warnings, ...codeMap.mappings.flatMap((mapping) => mapping.warnings)],
    outputPaths: {
      codeMap: portablePathFrom(repoRoot, outputPaths.codeMap),
      summaryMarkdown: portablePathFrom(repoRoot, outputPaths.summaryMarkdown),
    },
  };
}
