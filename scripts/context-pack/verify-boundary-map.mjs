#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { globSync } from 'glob';
import yaml from 'yaml';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_MAP_PATH = 'spec/context-pack/boundary-map.json';
const DEFAULT_SCHEMA_PATH = 'schema/context-pack-boundary-map.schema.json';
const DEFAULT_REPORT_JSON = 'artifacts/context-pack/context-pack-boundary-map-report.json';
const DEFAULT_REPORT_MD = 'artifacts/context-pack/context-pack-boundary-map-report.md';

const normalizePath = (value) => value.replace(/\\/g, '/');
const toRelativePath = (absolutePath) => normalizePath(path.relative(process.cwd(), absolutePath) || '.');

function printHelp() {
  process.stdout.write(`Context Pack Boundary Map validator

Usage:
  node scripts/context-pack/verify-boundary-map.mjs [options]

Options:
  --map <path>                  Boundary map JSON path (default: ${DEFAULT_MAP_PATH})
  --schema <path>               JSON Schema path (default: ${DEFAULT_SCHEMA_PATH})
  --report-json <path>          JSON report path (default: ${DEFAULT_REPORT_JSON})
  --report-md <path>            Markdown report path (default: ${DEFAULT_REPORT_MD})
  --context-pack-sources <glob> Override context-pack source glob (repeatable, comma-separated)
  --help, -h                    Show this help
`);
}

function splitPatterns(rawValue) {
  const chunks = [];
  let buffer = '';
  let braceDepth = 0;
  for (const char of rawValue) {
    if (char === '{') {
      braceDepth += 1;
      buffer += char;
      continue;
    }
    if (char === '}') {
      braceDepth = Math.max(0, braceDepth - 1);
      buffer += char;
      continue;
    }
    if (char === ',' && braceDepth === 0) {
      const trimmed = buffer.trim();
      if (trimmed.length > 0) {
        chunks.push(trimmed);
      }
      buffer = '';
      continue;
    }
    buffer += char;
  }
  const tail = buffer.trim();
  if (tail.length > 0) {
    chunks.push(tail);
  }
  return chunks;
}

function parseArgs(argv) {
  const options = {
    mapPath: DEFAULT_MAP_PATH,
    schemaPath: DEFAULT_SCHEMA_PATH,
    reportJsonPath: DEFAULT_REPORT_JSON,
    reportMarkdownPath: DEFAULT_REPORT_MD,
    contextPackSourcesOverride: [],
    help: false,
  };

  const appendSources = (rawValue) => {
    for (const value of splitPatterns(rawValue)) {
      options.contextPackSourcesOverride.push(value);
    }
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--map') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --map');
      }
      options.mapPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--map=')) {
      options.mapPath = arg.slice('--map='.length);
      continue;
    }
    if (arg === '--schema') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --schema');
      }
      options.schemaPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--schema=')) {
      options.schemaPath = arg.slice('--schema='.length);
      continue;
    }
    if (arg === '--report-json') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --report-json');
      }
      options.reportJsonPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--report-json=')) {
      options.reportJsonPath = arg.slice('--report-json='.length);
      continue;
    }
    if (arg === '--report-md') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --report-md');
      }
      options.reportMarkdownPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--report-md=')) {
      options.reportMarkdownPath = arg.slice('--report-md='.length);
      continue;
    }
    if (arg === '--context-pack-sources') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --context-pack-sources');
      }
      appendSources(next);
      index += 1;
      continue;
    }
    if (arg.startsWith('--context-pack-sources=')) {
      appendSources(arg.slice('--context-pack-sources='.length));
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function loadJsonFile(filePath) {
  const resolvedPath = path.resolve(filePath);
  if (!fs.existsSync(resolvedPath)) {
    throw new Error(`file not found: ${resolvedPath}`);
  }
  try {
    const data = JSON.parse(fs.readFileSync(resolvedPath, 'utf8'));
    return { resolvedPath, data };
  } catch (error) {
    throw new Error(`failed to parse JSON: ${resolvedPath} (${error instanceof Error ? error.message : String(error)})`);
  }
}

function validateMapSchema(payload, schemaPath) {
  const schemaRaw = fs.readFileSync(schemaPath, 'utf8');
  const schema = JSON.parse(schemaRaw);
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const valid = validate(payload);
  if (valid) {
    return [];
  }
  return (validate.errors ?? []).map((error) => ({
    type: 'boundary-map-schema-invalid',
    severity: 'error',
    message: `${error.instancePath || '/'} ${error.message || 'schema validation failed'}`,
    rule: error.keyword,
  }));
}

function discoverSources(sourcePatterns) {
  const matched = new Set();
  for (const pattern of sourcePatterns) {
    const files = globSync(pattern, {
      nodir: true,
      absolute: true,
      ignore: ['**/node_modules/**', '**/.git/**'],
    });
    for (const filePath of files) {
      matched.add(path.normalize(filePath));
    }
  }
  return Array.from(matched).sort((left, right) => left.localeCompare(right));
}

function parseContextPackFile(filePath) {
  const raw = fs.readFileSync(filePath, 'utf8');
  const lowerPath = filePath.toLowerCase();
  if (lowerPath.endsWith('.yml') || lowerPath.endsWith('.yaml')) {
    return yaml.parse(raw);
  }
  return JSON.parse(raw);
}

function isAuxiliaryContextPackPayload(payload) {
  if (!payload || typeof payload !== 'object') {
    return false;
  }
  return typeof payload.schemaVersion === 'string' && payload.schemaVersion.startsWith('context-pack-');
}

function toUniqueIds(input) {
  if (!Array.isArray(input)) {
    return [];
  }
  const ids = input
    .map((value) => (value && typeof value === 'object' ? value.id : undefined))
    .filter((value) => typeof value === 'string' && value.trim().length > 0)
    .map((value) => value.trim());
  return Array.from(new Set(ids));
}

function toUniqueStrings(input) {
  if (!Array.isArray(input)) {
    return [];
  }
  const values = input
    .filter((value) => typeof value === 'string' && value.trim().length > 0)
    .map((value) => value.trim());
  return Array.from(new Set(values));
}

function collectContextPackRefs(contextPackFiles, violations) {
  const refsByKind = {
    object: new Set(),
    morphism: new Set(),
    diagram: new Set(),
    'acceptance-test': new Set(),
    'forbidden-change': new Set(),
  };
  let scannedFiles = 0;
  let skippedAuxiliaryFiles = 0;

  for (const filePath of contextPackFiles) {
    try {
      const payload = parseContextPackFile(filePath);
      if (!payload || typeof payload !== 'object') {
        continue;
      }
      if (isAuxiliaryContextPackPayload(payload)) {
        skippedAuxiliaryFiles += 1;
        continue;
      }
      scannedFiles += 1;
      for (const id of toUniqueIds(payload.objects)) {
        refsByKind.object.add(id);
      }
      for (const id of toUniqueIds(payload.morphisms)) {
        refsByKind.morphism.add(id);
      }
      for (const id of toUniqueIds(payload.diagrams)) {
        refsByKind.diagram.add(id);
      }
      for (const id of toUniqueIds(payload.acceptance_tests)) {
        refsByKind['acceptance-test'].add(id);
      }
      for (const value of toUniqueStrings(payload.forbidden_changes)) {
        refsByKind['forbidden-change'].add(value);
      }
    } catch (error) {
      violations.push({
        type: 'context-pack-parse-failed',
        severity: 'error',
        source: toRelativePath(filePath),
        message: `failed to parse context-pack source '${toRelativePath(filePath)}': ${error instanceof Error ? error.message : String(error)}`,
      });
    }
  }

  return {
    refsByKind,
    scannedFiles,
    skippedAuxiliaryFiles,
  };
}

function hasContextPackRef(metadata, ref) {
  const set = metadata.refsByKind[ref.kind];
  return set instanceof Set && set.has(ref.refId);
}

function makeRefKey(ref) {
  return `${ref.kind}:${ref.refId}`;
}

function canonicalCycle(cycleNodes) {
  if (cycleNodes.length === 0) {
    return '';
  }
  const nodes = cycleNodes.slice(0, -1);
  const rotations = nodes.map((_, index) => {
    const rotated = nodes.slice(index).concat(nodes.slice(0, index));
    return rotated.concat(rotated[0]).join(' -> ');
  });
  return rotations.sort((left, right) => left.localeCompare(right))[0];
}

function detectCycles(edges) {
  const visited = new Set();
  const visiting = new Set();
  const stack = [];
  const seenCycles = new Set();
  const cycles = [];

  const visit = (node) => {
    visiting.add(node);
    stack.push(node);

    for (const next of edges.get(node) ?? []) {
      if (!visited.has(next) && !visiting.has(next)) {
        visit(next);
        continue;
      }
      if (visiting.has(next)) {
        const startIndex = stack.indexOf(next);
        const cycleNodes = stack.slice(startIndex).concat(next);
        const signature = canonicalCycle(cycleNodes);
        if (!seenCycles.has(signature)) {
          seenCycles.add(signature);
          cycles.push(cycleNodes);
        }
      }
    }

    stack.pop();
    visiting.delete(node);
    visited.add(node);
  };

  for (const node of edges.keys()) {
    if (!visited.has(node)) {
      visit(node);
    }
  }

  return cycles;
}

function validateBoundaryMap(metadata, slices, violations) {
  const sliceMap = new Map();
  const producerByRef = new Map();
  const edges = new Map();
  const stats = {
    checkedSlices: 0,
    checkedProduces: 0,
    checkedConsumes: 0,
    duplicateSliceIds: 0,
    missingContextPackRefs: 0,
    duplicateProducedRefs: 0,
    missingUpstreamSlices: 0,
    missingUpstreamProducers: 0,
    cycleViolations: 0,
  };

  for (const slice of Array.isArray(slices) ? slices : []) {
    stats.checkedSlices += 1;
    const sliceId = typeof slice.id === 'string' ? slice.id.trim() : '';
    if (sliceMap.has(sliceId)) {
      stats.duplicateSliceIds += 1;
      violations.push({
        type: 'boundary-slice-duplicate',
        severity: 'error',
        sliceId,
        message: `slice '${sliceId}' is defined more than once`,
      });
      continue;
    }
    sliceMap.set(sliceId, slice);
    edges.set(sliceId, new Set());
  }

  for (const [sliceId, slice] of sliceMap.entries()) {
    for (const ref of Array.isArray(slice.produces) ? slice.produces : []) {
      stats.checkedProduces += 1;
      if (!hasContextPackRef(metadata, ref)) {
        stats.missingContextPackRefs += 1;
        violations.push({
          type: 'boundary-ref-missing',
          severity: 'error',
          sliceId,
          kind: ref.kind,
          refId: ref.refId,
          direction: 'produces',
          message: `slice '${sliceId}' produces ${ref.kind} '${ref.refId}' but the ref does not exist in context-pack sources`,
        });
        continue;
      }
      const refKey = makeRefKey(ref);
      const existingProducer = producerByRef.get(refKey);
      if (existingProducer && existingProducer !== sliceId) {
        stats.duplicateProducedRefs += 1;
        violations.push({
          type: 'boundary-producer-duplicate',
          severity: 'error',
          sliceId,
          kind: ref.kind,
          refId: ref.refId,
          rule: existingProducer,
          message: `ref ${ref.kind} '${ref.refId}' is produced by both '${existingProducer}' and '${sliceId}'`,
        });
        continue;
      }
      producerByRef.set(refKey, sliceId);
    }
  }

  for (const [sliceId, slice] of sliceMap.entries()) {
    for (const ref of Array.isArray(slice.consumes) ? slice.consumes : []) {
      stats.checkedConsumes += 1;
      if (!hasContextPackRef(metadata, ref)) {
        stats.missingContextPackRefs += 1;
        violations.push({
          type: 'boundary-ref-missing',
          severity: 'error',
          sliceId,
          kind: ref.kind,
          refId: ref.refId,
          direction: 'consumes',
          message: `slice '${sliceId}' consumes ${ref.kind} '${ref.refId}' but the ref does not exist in context-pack sources`,
        });
        continue;
      }

      if (!ref.upstream || ref.upstream.type !== 'slice') {
        continue;
      }

      const upstreamSliceId = ref.upstream.sliceId;
      if (!sliceMap.has(upstreamSliceId)) {
        stats.missingUpstreamSlices += 1;
        violations.push({
          type: 'boundary-upstream-slice-missing',
          severity: 'error',
          sliceId,
          kind: ref.kind,
          refId: ref.refId,
          rule: upstreamSliceId,
          message: `slice '${sliceId}' consumes ${ref.kind} '${ref.refId}' from missing upstream slice '${upstreamSliceId}'`,
        });
        continue;
      }

      edges.get(sliceId)?.add(upstreamSliceId);
      const actualProducer = producerByRef.get(makeRefKey(ref));
      if (actualProducer !== upstreamSliceId) {
        stats.missingUpstreamProducers += 1;
        const detail = actualProducer
          ? `actual producer is '${actualProducer}'`
          : 'no slice produces the ref';
        violations.push({
          type: 'boundary-upstream-producer-missing',
          severity: 'error',
          sliceId,
          kind: ref.kind,
          refId: ref.refId,
          rule: upstreamSliceId,
          message: `slice '${sliceId}' consumes ${ref.kind} '${ref.refId}' from '${upstreamSliceId}', but ${detail}`,
        });
      }
    }
  }

  const cycles = detectCycles(edges);
  stats.cycleViolations = cycles.length;
  for (const cycleNodes of cycles) {
    violations.push({
      type: 'boundary-slice-cycle',
      severity: 'error',
      sliceId: cycleNodes[0],
      rule: 'slice-dependency-cycle',
      message: `slice dependency cycle detected: ${cycleNodes.join(' -> ')}`,
    });
  }

  return stats;
}

function summarizeViolations(violations, stats = {}) {
  const countByType = (type) => violations.filter((entry) => entry.type === type).length;
  return {
    totalViolations: violations.length,
    duplicateSliceIds:
      Number.isFinite(stats.duplicateSliceIds) && stats.duplicateSliceIds >= 0
        ? stats.duplicateSliceIds
        : countByType('boundary-slice-duplicate'),
    missingContextPackRefs:
      Number.isFinite(stats.missingContextPackRefs) && stats.missingContextPackRefs >= 0
        ? stats.missingContextPackRefs
        : countByType('boundary-ref-missing'),
    duplicateProducedRefs:
      Number.isFinite(stats.duplicateProducedRefs) && stats.duplicateProducedRefs >= 0
        ? stats.duplicateProducedRefs
        : countByType('boundary-producer-duplicate'),
    missingUpstreamSlices:
      Number.isFinite(stats.missingUpstreamSlices) && stats.missingUpstreamSlices >= 0
        ? stats.missingUpstreamSlices
        : countByType('boundary-upstream-slice-missing'),
    missingUpstreamProducers:
      Number.isFinite(stats.missingUpstreamProducers) && stats.missingUpstreamProducers >= 0
        ? stats.missingUpstreamProducers
        : countByType('boundary-upstream-producer-missing'),
    cycleViolations:
      Number.isFinite(stats.cycleViolations) && stats.cycleViolations >= 0
        ? stats.cycleViolations
        : countByType('boundary-slice-cycle'),
  };
}

function escapeMarkdownTableCell(value) {
  return String(value ?? '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/`/g, '\\`')
    .replace(/\|/g, '\\|')
    .replace(/\r?\n/g, '<br>');
}

function buildMarkdownReport(report) {
  const lines = [
    '# Context Pack Boundary Map Validation Report',
    '',
    `- GeneratedAt: ${report.generatedAt}`,
    `- Status: ${report.status.toUpperCase()}`,
    `- Map: \`${report.mapPath}\``,
    `- Schema: \`${report.schemaPath}\``,
    `- Context pack files: ${report.scannedContextPackFiles}`,
    `- Skipped auxiliary files: ${report.skippedAuxiliaryFiles}`,
    `- Checked slices: ${report.checkedSlices}`,
    `- Produced refs: ${report.checkedProduces}`,
    `- Consumed refs: ${report.checkedConsumes}`,
    `- Violations: ${report.summary.totalViolations}`,
    '',
    '## Summary',
    `- duplicate slice ids: ${report.summary.duplicateSliceIds}`,
    `- missing context-pack refs: ${report.summary.missingContextPackRefs}`,
    `- duplicate produced refs: ${report.summary.duplicateProducedRefs}`,
    `- missing upstream slices: ${report.summary.missingUpstreamSlices}`,
    `- missing upstream producers: ${report.summary.missingUpstreamProducers}`,
    `- slice dependency cycles: ${report.summary.cycleViolations}`,
    '',
  ];

  if (report.violations.length === 0) {
    lines.push('## Violations', '', 'No violations detected.');
    return `${lines.join('\n')}\n`;
  }

  lines.push('## Violations', '', '| Type | Slice | Ref | Rule | Message |', '| --- | --- | --- | --- | --- |');
  for (const violation of report.violations) {
    const ref = violation.kind && violation.refId ? `${violation.kind}:${violation.refId}` : '-';
    lines.push(
      `| ${escapeMarkdownTableCell(violation.type)} | ${escapeMarkdownTableCell(violation.sliceId || '-')} | ${escapeMarkdownTableCell(ref)} | ${escapeMarkdownTableCell(violation.rule || '-')} | ${escapeMarkdownTableCell(violation.message)} |`,
    );
  }
  return `${lines.join('\n')}\n`;
}

function writeReport(report, reportJsonPath, reportMarkdownPath) {
  const resolvedJsonPath = path.resolve(reportJsonPath);
  const resolvedMarkdownPath = path.resolve(reportMarkdownPath);
  fs.mkdirSync(path.dirname(resolvedJsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(resolvedMarkdownPath), { recursive: true });
  fs.writeFileSync(resolvedJsonPath, `${JSON.stringify(report, null, 2)}\n`);
  fs.writeFileSync(resolvedMarkdownPath, buildMarkdownReport(report));
}

function validateBoundaryMapCli(options) {
  const { resolvedPath: resolvedMapPath, data: mapPayload } = loadJsonFile(options.mapPath);
  const resolvedSchemaPath = path.resolve(options.schemaPath);
  const violations = [...validateMapSchema(mapPayload, resolvedSchemaPath)];
  const mapValue = mapPayload && typeof mapPayload === 'object' && !Array.isArray(mapPayload) ? mapPayload : {};
  const sourcePatterns =
    options.contextPackSourcesOverride.length > 0
      ? options.contextPackSourcesOverride
      : Array.isArray(mapValue.contextPackSources)
        ? mapValue.contextPackSources
        : [];

  const discoveredContextPackFiles = discoverSources(sourcePatterns);
  const normalizedMapPath = path.normalize(resolvedMapPath);
  const contextPackFiles = discoveredContextPackFiles.filter((sourcePath) => path.normalize(sourcePath) !== normalizedMapPath);
  if (contextPackFiles.length === 0) {
    violations.push({
      type: 'context-pack-sources-empty',
      severity: 'error',
      message: `No context-pack files matched source patterns: ${sourcePatterns.join(', ')}`,
    });
  }

  const metadata = collectContextPackRefs(contextPackFiles, violations);
  const stats = validateBoundaryMap(metadata, mapValue.slices, violations);
  const report = {
    schemaVersion: 'context-pack-boundary-map-report/v1',
    generatedAt: new Date().toISOString(),
    mapPath: toRelativePath(resolvedMapPath),
    schemaPath: toRelativePath(resolvedSchemaPath),
    contextPackSources: sourcePatterns,
    scannedContextPackFiles: metadata.scannedFiles,
    skippedAuxiliaryFiles: metadata.skippedAuxiliaryFiles,
    contextPackObjectCount: metadata.refsByKind.object.size,
    contextPackMorphismCount: metadata.refsByKind.morphism.size,
    contextPackDiagramCount: metadata.refsByKind.diagram.size,
    contextPackAcceptanceTestCount: metadata.refsByKind['acceptance-test'].size,
    contextPackForbiddenChangeCount: metadata.refsByKind['forbidden-change'].size,
    checkedSlices: stats.checkedSlices,
    checkedProduces: stats.checkedProduces,
    checkedConsumes: stats.checkedConsumes,
    summary: summarizeViolations(violations, stats),
    status: violations.length === 0 ? 'pass' : 'fail',
    violations,
  };

  writeReport(report, options.reportJsonPath, options.reportMarkdownPath);
  process.stdout.write(`[context-pack:boundary-map] report(json): ${toRelativePath(path.resolve(options.reportJsonPath))}\n`);
  process.stdout.write(`[context-pack:boundary-map] report(md): ${toRelativePath(path.resolve(options.reportMarkdownPath))}\n`);

  if (report.status === 'fail') {
    process.stderr.write(`[context-pack:boundary-map] validation failed (${violations.length} violation(s))\n`);
    return 2;
  }
  process.stdout.write(
    `[context-pack:boundary-map] validation passed (${stats.checkedSlices} slice(s), ${stats.checkedConsumes} consume edge(s) checked)\n`,
  );
  return 0;
}

try {
  const options = parseArgs(process.argv);
  if (options.help) {
    printHelp();
    process.exit(0);
  }
  process.exit(validateBoundaryMapCli(options));
} catch (error) {
  process.stderr.write(`[context-pack:boundary-map] ${error instanceof Error ? error.message : String(error)}\n`);
  process.exit(1);
}
