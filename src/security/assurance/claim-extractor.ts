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
type Criticality = 'low' | 'medium' | 'high' | 'critical';

export interface ClaimExtractionOptions {
  generatedAt?: string;
  repoRoot?: string;
  validate?: boolean;
}

export interface ClaimExtractionWarning {
  code: string;
  source: string;
  path: string;
  message: string;
}

export interface ClaimExtractionOutputPaths {
  claims: string;
  summaryMarkdown: string;
}

export interface ClaimExtractionResult {
  generatedAt: string;
  claims: SecurityClaimDocument;
  warnings: ClaimExtractionWarning[];
  outputPaths: ClaimExtractionOutputPaths;
}

type SecurityClaimDocument = {
  schemaVersion: 'security-claim/v1';
  generatedAt: string;
  claims: JsonRecord[];
  summary: {
    totalClaims: number;
    byCriticality: Record<Criticality, number>;
  };
};

type ParsedClaimBlock = {
  fields: Map<string, string>;
  startLine: number;
  section?: string;
};

const GENERATOR = 'security-claim-extractor';
const MODULE_DIR = path.dirname(fileURLToPath(import.meta.url));
const CRITICALITIES = ['low', 'medium', 'high', 'critical'] as const;

function warning(warnings: ClaimExtractionWarning[], code: string, source: string, pathRef: string, message: string): void {
  warnings.push({ code, source, path: pathRef, message });
}

function formatId(index: number): string {
  return `SEC-CLAIM-${String(index + 1).padStart(3, '0')}`;
}

function nextAvailableClaimId(usedIds: Set<string>, reservedIds: Set<string>): string {
  for (let index = 0; index < Number.MAX_SAFE_INTEGER; index += 1) {
    const candidate = formatId(index);
    if (!usedIds.has(candidate) && !reservedIds.has(candidate)) {
      return candidate;
    }
  }
  throw new Error('Unable to allocate a unique SEC-CLAIM id.');
}

function claimIdForBlock(
  block: ParsedClaimBlock,
  index: number,
  usedIds: Set<string>,
  reservedIds: Set<string>,
  warnings: ClaimExtractionWarning[],
  source: string,
): string {
  const rawId = block.fields.get('id');
  const explicitId = rawId && rawId.trim().length > 0 ? rawId.trim() : undefined;
  if (rawId !== undefined && explicitId === undefined) {
    warning(
      warnings,
      'empty-id-normalized',
      source,
      `/claims/${index}/id`,
      `Empty explicit security claim id at line ${block.startLine} was ignored and replaced with a generated id.`,
    );
  }
  const candidate = explicitId ?? formatId(index);
  if (!usedIds.has(candidate) && (explicitId !== undefined || !reservedIds.has(candidate))) {
    usedIds.add(candidate);
    return candidate;
  }
  const replacement = nextAvailableClaimId(usedIds, reservedIds);
  usedIds.add(replacement);
  warning(
    warnings,
    'id-collision-normalized',
    source,
    `/claims/${index}/id`,
    `Security claim id '${candidate}' at line ${block.startLine} collided during extraction and was normalized to '${replacement}'.`,
  );
  return replacement;
}

function countCriticality(): Record<Criticality, number> {
  return { low: 0, medium: 0, high: 0, critical: 0 };
}

function normalizeKey(key: string): string {
  return key.trim().replace(/[\s_-]+/g, '').toLowerCase();
}

function splitList(value: string | undefined): string[] {
  if (!value) {
    return [];
  }
  const entries = value
    .replace(/^\[/, '')
    .replace(/\]$/, '')
    .split(/[|,]/)
    .map((entry) => entry.trim())
    .filter((entry) => entry.length > 0);
  return [...new Set(entries)];
}

function parseBoolean(value: string | undefined, fallback: boolean): boolean {
  const normalized = value?.trim().toLowerCase();
  if (normalized === 'true' || normalized === 'yes' || normalized === '1') {
    return true;
  }
  if (normalized === 'false' || normalized === 'no' || normalized === '0') {
    return false;
  }
  return fallback;
}

function setIfPresent(target: JsonRecord, key: string, value: string | undefined): void {
  if (value !== undefined && value.trim().length > 0) {
    target[key] = value.trim();
  }
}

function pushUnknownFieldWarnings(
  warnings: ClaimExtractionWarning[],
  source: string,
  block: ParsedClaimBlock,
  index: number,
  knownKeys: ReadonlySet<string>,
): void {
  for (const key of block.fields.keys()) {
    if (!knownKeys.has(key)) {
      warning(
        warnings,
        'unsupported-field',
        source,
        `/claims/${index}/${key}`,
        `Unsupported SEC-CLAIM field '${key}' at line ${block.startLine} was ignored during extraction.`,
      );
    }
  }
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
    if (existsSync(path.join(candidate, 'schema/security-claim-v1.schema.json'))) {
      return candidate;
    }
  }
  throw new Error('Unable to locate ae-framework schema directory for security claim validation.');
}

function outputPathsFor(outPath: string): ClaimExtractionOutputPaths {
  const resolvedOut = path.resolve(outPath);
  if (path.extname(resolvedOut).toLowerCase() === '.json') {
    return {
      claims: resolvedOut,
      summaryMarkdown: resolvedOut.replace(/\.json$/i, '.md'),
    };
  }
  return {
    claims: path.join(resolvedOut, 'security-claims.json'),
    summaryMarkdown: path.join(resolvedOut, 'security-claims.md'),
  };
}

function parseClaimBlocks(markdown: string, source: string, warnings: ClaimExtractionWarning[]): ParsedClaimBlock[] {
  const lines = markdown.split(/\r?\n/);
  const blocks: ParsedClaimBlock[] = [];
  let currentSection: string | undefined;
  let fenceMarker: string | undefined;

  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index] ?? '';
    const fence = line.trim().match(/^(```+|~~~+)/);
    if (fence?.[1]) {
      const marker = fence[1].startsWith('`') ? '```' : '~~~';
      fenceMarker = fenceMarker === marker ? undefined : marker;
      continue;
    }
    if (fenceMarker) {
      continue;
    }
    const heading = line.match(/^#{1,6}\s+(.+)$/);
    if (heading?.[1]) {
      currentSection = heading[1].trim();
    }

    if (line.trim() !== 'SEC-CLAIM:') {
      continue;
    }

    const fields = new Map<string, string>();
    let cursor = index + 1;
    for (; cursor < lines.length; cursor += 1) {
      const candidate = lines[cursor] ?? '';
      const trimmed = candidate.trim();
      if (trimmed.length === 0 || trimmed === 'SEC-CLAIM:' || /^#{1,6}\s+/.test(trimmed)) {
        break;
      }
      const separator = candidate.indexOf(':');
      if (separator <= 0) {
        warning(
          warnings,
          'ignored-line',
          source,
          `/lines/${cursor + 1}`,
          `Ignored SEC-CLAIM line without key/value separator: '${trimmed}'.`,
        );
        continue;
      }
      const key = normalizeKey(candidate.slice(0, separator));
      const value = candidate.slice(separator + 1).trim();
      fields.set(key, value);
    }

    blocks.push({
      fields,
      startLine: index + 1,
      ...(currentSection !== undefined ? { section: currentSection } : {}),
    });
    index = cursor - 1;
  }

  return blocks;
}

function sourceRefFor(block: ParsedClaimBlock, specPath: string, repoRoot: string): JsonRecord {
  const sourceRef: JsonRecord = {
    kind: block.fields.get('sourcekind') ?? 'spec',
    uri: block.fields.get('sourceuri') ?? portablePathFrom(repoRoot, specPath),
  };
  setIfPresent(sourceRef, 'section', block.fields.get('sourcesection') ?? block.section);
  setIfPresent(sourceRef, 'description', block.fields.get('sourcedescription'));
  return sourceRef;
}

function trustBoundaryFor(block: ParsedClaimBlock): JsonRecord {
  const entryPoints = splitList(block.fields.get('entrypoints'));
  const boundaryIds = splitList(block.fields.get('boundaryids'));
  const dataClasses = splitList(block.fields.get('dataclasses'));
  const notes = splitList(block.fields.get('trustboundarynotes'));
  return {
    ...(boundaryIds.length > 0 ? { boundaryIds } : {}),
    entryPoints: entryPoints.length > 0 ? entryPoints : ['unspecified'],
    attackerControlled: parseBoolean(block.fields.get('attackercontrolled'), true),
    ...(dataClasses.length > 0 ? { dataClasses } : {}),
    ...(notes.length > 0 ? { notes } : {}),
  };
}

function claimForBlock(block: ParsedClaimBlock, claimId: string, specPath: string, repoRoot: string): JsonRecord {
  const stride = splitList(block.fields.get('stride'));
  const cwe = splitList(block.fields.get('cwe'));
  const requiredLanes = splitList(block.fields.get('requiredlanes'));
  const threatTags: JsonRecord = {
    stride: stride.length > 0 ? stride : ['Tampering'],
    cwe: cwe.length > 0 ? cwe : ['CWE-20'],
  };
  const provenance: JsonRecord = {
    origin: block.fields.get('provenanceorigin') ?? block.fields.get('origin') ?? 'manual-block',
    generator: block.fields.get('generator') ?? GENERATOR,
    source: portablePathFrom(repoRoot, specPath),
  };
  setIfPresent(provenance, 'version', block.fields.get('version'));

  const claim: JsonRecord = {
    id: claimId,
    type: block.fields.get('type') ?? 'invariant',
    sourceRefs: [sourceRefFor(block, specPath, repoRoot)],
    criticality: block.fields.get('criticality') ?? 'medium',
    targetLevel: block.fields.get('targetlevel') ?? 'A2',
    threatTags,
    trustBoundary: trustBoundaryFor(block),
    requiredLanes: requiredLanes.length > 0 ? requiredLanes : ['spec', 'adversarial'],
    provenance,
  };
  setIfPresent(claim, 'statement', block.fields.get('statement'));
  const notes = splitList(block.fields.get('notes'));
  if (notes.length > 0) {
    claim['notes'] = notes;
  }
  return claim;
}

function knownFieldKeys(): ReadonlySet<string> {
  return new Set([
    'id',
    'type',
    'statement',
    'sourcekind',
    'sourceuri',
    'sourcesection',
    'sourcedescription',
    'criticality',
    'targetlevel',
    'stride',
    'cwe',
    'entrypoints',
    'boundaryids',
    'attackercontrolled',
    'dataclasses',
    'trustboundarynotes',
    'requiredlanes',
    'provenanceorigin',
    'origin',
    'generator',
    'version',
    'notes',
  ]);
}

function buildDocument(blocks: ParsedClaimBlock[], specPath: string, repoRoot: string, generatedAt: string, warnings: ClaimExtractionWarning[]): SecurityClaimDocument {
  const knownKeys = knownFieldKeys();
  const source = portablePathFrom(repoRoot, specPath);
  const usedIds = new Set<string>();
  const reservedIds = new Set(
    blocks
      .map((block) => block.fields.get('id'))
      .filter((id): id is string => Boolean(id?.startsWith('SEC-CLAIM-'))),
  );
  const claims = blocks.map((block, index) => {
    pushUnknownFieldWarnings(warnings, source, block, index, knownKeys);
    return claimForBlock(
      block,
      claimIdForBlock(block, index, usedIds, reservedIds, warnings, source),
      specPath,
      repoRoot,
    );
  });
  const byCriticality = countCriticality();
  for (const claim of claims) {
    const criticality = claim['criticality'];
    if (typeof criticality === 'string' && (CRITICALITIES as readonly string[]).includes(criticality)) {
      byCriticality[criticality as Criticality] += 1;
    }
  }
  return {
    schemaVersion: 'security-claim/v1',
    generatedAt,
    claims,
    summary: {
      totalClaims: claims.length,
      byCriticality,
    },
  };
}

async function validateClaims(repoRoot: string, document: SecurityClaimDocument): Promise<void> {
  const schema = JSON.parse(await fs.readFile(path.join(repoRoot, 'schema/security-claim-v1.schema.json'), 'utf8')) as unknown;
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  if (!validate(document)) {
    throw new Error(`Generated security claims failed schema validation: ${JSON.stringify(validate.errors, null, 2)}`);
  }
}

function renderSummaryMarkdown(document: SecurityClaimDocument, source: string, warnings: ClaimExtractionWarning[]): string {
  const lines = [
    '# Security claim extraction summary',
    '',
    `- Generated at: ${document.generatedAt}`,
    `- Source: ${source}`,
    `- Claims: ${document.claims.length}`,
    `- Warnings: ${warnings.length}`,
    '',
    '## Claims',
    '',
  ];
  for (const claim of document.claims) {
    const id = typeof claim['id'] === 'string' ? claim['id'] : 'unknown-claim';
    const criticality = typeof claim['criticality'] === 'string' ? claim['criticality'] : 'unknown-criticality';
    const statement = typeof claim['statement'] === 'string' ? claim['statement'] : 'missing statement';
    lines.push(`- \`${id}\` (${criticality}): ${statement}`);
  }
  lines.push('', '## Warnings', '');
  if (warnings.length === 0) {
    lines.push('- None');
  } else {
    for (const entry of warnings) {
      lines.push(`- \`${entry.code}\` ${entry.source}${entry.path}: ${entry.message}`);
    }
  }
  lines.push('');
  return lines.join('\n');
}

async function writeJson(filePath: string, value: unknown): Promise<void> {
  await fs.writeFile(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

export async function extractSecurityClaimsFromSpec(specPath: string, outPath: string, options: ClaimExtractionOptions = {}): Promise<ClaimExtractionResult> {
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const resolvedSpecPath = path.resolve(specPath);
  const repoRoot = resolveSchemaRoot(options.repoRoot);
  const source = portablePathFrom(repoRoot, resolvedSpecPath);
  const warnings: ClaimExtractionWarning[] = [];
  const markdown = await fs.readFile(resolvedSpecPath, 'utf8');
  const blocks = parseClaimBlocks(markdown, source, warnings);
  if (blocks.length === 0) {
    throw new Error(`No SEC-CLAIM blocks found in ${source}.`);
  }
  const claims = buildDocument(blocks, resolvedSpecPath, repoRoot, generatedAt, warnings);
  if (options.validate !== false) {
    await validateClaims(repoRoot, claims);
  }

  const outputPaths = outputPathsFor(outPath);
  await fs.mkdir(path.dirname(outputPaths.claims), { recursive: true });
  await writeJson(outputPaths.claims, claims);
  await fs.writeFile(outputPaths.summaryMarkdown, renderSummaryMarkdown(claims, source, warnings), 'utf8');

  return {
    generatedAt,
    claims,
    warnings,
    outputPaths: {
      claims: portablePathFrom(repoRoot, outputPaths.claims),
      summaryMarkdown: portablePathFrom(repoRoot, outputPaths.summaryMarkdown),
    },
  };
}
