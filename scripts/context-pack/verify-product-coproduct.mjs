#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { globSync } from 'glob';
import yaml from 'yaml';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_MAP_PATH = 'spec/context-pack/product-coproduct-map.json';
const DEFAULT_SCHEMA_PATH = 'schema/context-pack-product-coproduct.schema.json';
const DEFAULT_REPORT_JSON = 'artifacts/context-pack/context-pack-product-coproduct-report.json';
const DEFAULT_REPORT_MD = 'artifacts/context-pack/context-pack-product-coproduct-report.md';
const ROOT_DIR = path.resolve(process.cwd());
const GENERIC_DTO_KEYS = new Set(['data', 'payload', 'body', 'request', 'dto', 'params', 'input']);

const normalizePath = (value) => value.replace(/\\/g, '/');
const toRelativePath = (absolutePath) => normalizePath(path.relative(process.cwd(), absolutePath) || '.');

function printHelp() {
  process.stdout.write(`Context Pack Product/Coproduct validator

Usage:
  node scripts/context-pack/verify-product-coproduct.mjs [options]

Options:
  --map <path>                  Product/Coproduct map path (default: ${DEFAULT_MAP_PATH})
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
    type: 'product-coproduct-schema-invalid',
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

function toStringArray(value) {
  if (!Array.isArray(value)) {
    return [];
  }
  return value
    .filter((item) => typeof item === 'string')
    .map((item) => item.trim())
    .filter((item) => item.length > 0);
}

function isAuxiliaryContextPackPayload(payload) {
  if (!payload || typeof payload !== 'object') {
    return false;
  }
  return typeof payload.schemaVersion === 'string' && payload.schemaVersion.startsWith('context-pack-');
}

function isInsideRepository(candidatePath) {
  const relative = path.relative(ROOT_DIR, candidatePath);
  return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
}

function mergeSet(target, values) {
  for (const value of values) {
    target.add(value);
  }
}

function collectContextMorphisms(contextPackFiles, violations) {
  const morphisms = new Map();
  for (const filePath of contextPackFiles) {
    try {
      const payload = parseContextPackFile(filePath);
      if (!payload || typeof payload !== 'object' || isAuxiliaryContextPackPayload(payload)) {
        continue;
      }
      const entries = Array.isArray(payload.morphisms) ? payload.morphisms : [];
      for (const entry of entries) {
        if (!entry || typeof entry !== 'object' || typeof entry.id !== 'string' || entry.id.trim().length === 0) {
          continue;
        }
        const id = entry.id.trim();
        const existing = morphisms.get(id) ?? {
          id,
          inputKeys: new Set(),
          failures: new Set(),
          files: new Set(),
        };
        const inputKeys =
          entry.input && typeof entry.input === 'object' && !Array.isArray(entry.input)
            ? Object.keys(entry.input)
            : [];
        mergeSet(existing.inputKeys, inputKeys);
        mergeSet(existing.failures, toStringArray(entry.failures));
        existing.files.add(toRelativePath(filePath));
        morphisms.set(id, existing);
      }
    } catch (error) {
      violations.push({
        type: 'context-pack-parse-error',
        severity: 'error',
        file: toRelativePath(filePath),
        message: error instanceof Error ? error.message : String(error),
      });
    }
  }
  return morphisms;
}

function hasGlobPattern(value) {
  return /[*?\[\]{}!]/.test(value);
}

function resolveEvidenceTargets(value) {
  if (hasGlobPattern(value)) {
    const matches = globSync(value, {
      nodir: true,
      absolute: true,
      ignore: ['**/node_modules/**', '**/.git/**'],
    });
    return matches
      .map((candidate) => path.resolve(candidate))
      .filter((candidate) => isInsideRepository(candidate));
  }

  const resolved = path.resolve(value);
  if (!isInsideRepository(resolved)) {
    return [];
  }
  if (!fs.existsSync(resolved) || !fs.statSync(resolved).isFile()) {
    return [];
  }
  return [resolved];
}

function toMapByMorphism(entries, keyName, violations, duplicateType) {
  const mapping = new Map();
  for (const entry of entries) {
    if (!entry || typeof entry !== 'object' || typeof entry[keyName] !== 'string') {
      continue;
    }
    const morphismId = entry[keyName].trim();
    if (mapping.has(morphismId)) {
      violations.push({
        type: duplicateType,
        severity: 'error',
        morphismId,
        message: `Duplicate mapping for morphism '${morphismId}'`,
      });
      continue;
    }
    mapping.set(morphismId, entry);
  }
  return mapping;
}

function validateProducts(contextMorphisms, productEntries, violations) {
  const productMappings = toMapByMorphism(
    Array.isArray(productEntries) ? productEntries : [],
    'morphismId',
    violations,
    'product-mapping-duplicate',
  );
  let inputCoverageGaps = 0;
  let ambiguousDtoKeys = 0;

  for (const morphismId of contextMorphisms.keys()) {
    if (!productMappings.has(morphismId)) {
      violations.push({
        type: 'product-mapping-missing',
        severity: 'error',
        morphismId,
        message: `Product mapping is missing for morphism '${morphismId}'`,
      });
    }
  }

  for (const [morphismId, mapping] of productMappings.entries()) {
    const context = contextMorphisms.get(morphismId);
    if (!context) {
      violations.push({
        type: 'product-mapping-unknown',
        severity: 'error',
        morphismId,
        message: `Product mapping references unknown morphism '${morphismId}'`,
      });
      continue;
    }

    const requiredInputKeys = toStringArray(mapping.requiredInputKeys);
    const requiredSet = new Set(requiredInputKeys);
    if (requiredSet.size !== requiredInputKeys.length) {
      violations.push({
        type: 'product-required-input-duplicate',
        severity: 'error',
        morphismId,
        message: `requiredInputKeys includes duplicates for '${morphismId}'`,
      });
    }

    const contextInputKeys = Array.from(context.inputKeys);
    for (const key of requiredSet) {
      if (!context.inputKeys.has(key)) {
        inputCoverageGaps += 1;
        violations.push({
          type: 'product-required-input-unknown',
          severity: 'error',
          morphismId,
          message: `requiredInputKeys contains unknown key '${key}' for '${morphismId}'`,
        });
      }
    }

    for (const key of contextInputKeys) {
      if (!requiredSet.has(key)) {
        inputCoverageGaps += 1;
        violations.push({
          type: 'product-required-input-missing',
          severity: 'error',
          morphismId,
          message: `Product mapping is missing required input key '${key}' for '${morphismId}'`,
        });
      }
    }

    if (mapping.disallowGenericDtoKeys === true) {
      const keysToCheck = new Set([...context.inputKeys, ...requiredSet]);
      for (const key of keysToCheck) {
        if (GENERIC_DTO_KEYS.has(key)) {
          ambiguousDtoKeys += 1;
          violations.push({
            type: 'ambiguous-dto-key',
            severity: 'error',
            morphismId,
            rule: key,
            message: `Ambiguous DTO key '${key}' is not allowed for '${morphismId}'`,
          });
        }
      }
    }
  }

  return {
    productMappings,
    inputCoverageGaps,
    ambiguousDtoKeys,
  };
}

function validateCoproducts(contextMorphisms, coproductEntries, violations) {
  const coproductMappings = toMapByMorphism(
    Array.isArray(coproductEntries) ? coproductEntries : [],
    'morphismId',
    violations,
    'coproduct-mapping-duplicate',
  );
  let missingEvidence = 0;
  let variantCoverageGaps = 0;
  let totalFailureVariants = 0;
  let coveredFailureVariants = 0;

  for (const context of contextMorphisms.values()) {
    totalFailureVariants += context.failures.size;
    if (!coproductMappings.has(context.id)) {
      if (context.failures.size > 0) {
        variantCoverageGaps += context.failures.size;
      }
      violations.push({
        type: 'coproduct-mapping-missing',
        severity: 'error',
        morphismId: context.id,
        message: `Coproduct mapping is missing for morphism '${context.id}'`,
      });
      continue;
    }
  }

  for (const [morphismId, mapping] of coproductMappings.entries()) {
    const context = contextMorphisms.get(morphismId);
    if (!context) {
      violations.push({
        type: 'coproduct-mapping-unknown',
        severity: 'error',
        morphismId,
        message: `Coproduct mapping references unknown morphism '${morphismId}'`,
      });
      continue;
    }

    const variants = Array.isArray(mapping.variants) ? mapping.variants : [];
    const variantNames = new Set();
    for (const variant of variants) {
      if (!variant || typeof variant !== 'object' || typeof variant.name !== 'string') {
        continue;
      }
      const variantName = variant.name.trim();
      if (variantNames.has(variantName)) {
        violations.push({
          type: 'coproduct-variant-duplicate',
          severity: 'error',
          morphismId,
          rule: variantName,
          message: `Duplicate variant '${variantName}' for '${morphismId}'`,
        });
      }
      variantNames.add(variantName);

      const evidencePaths = toStringArray(variant.evidencePaths);
      for (const evidencePath of evidencePaths) {
        const matches = resolveEvidenceTargets(evidencePath);
        if (matches.length === 0) {
          missingEvidence += 1;
          violations.push({
            type: 'coproduct-evidence-missing',
            severity: 'error',
            morphismId,
            rule: variantName,
            message: `Evidence path not found for variant '${variantName}': ${evidencePath}`,
          });
        }
      }
    }

    for (const failure of context.failures) {
      if (!variantNames.has(failure)) {
        variantCoverageGaps += 1;
        violations.push({
          type: 'coproduct-variant-missing',
          severity: 'error',
          morphismId,
          rule: failure,
          message: `Failure variant '${failure}' is missing in coproduct mapping for '${morphismId}'`,
        });
      } else {
        coveredFailureVariants += 1;
      }
    }

    for (const variantName of variantNames) {
      if (!context.failures.has(variantName)) {
        violations.push({
          type: 'coproduct-variant-unknown',
          severity: 'error',
          morphismId,
          rule: variantName,
          message: `Coproduct variant '${variantName}' is not defined in context-pack failures for '${morphismId}'`,
        });
      }
    }
  }

  return {
    missingEvidence,
    variantCoverageGaps,
    totalFailureVariants,
    coveredFailureVariants,
  };
}

function summarizeViolations(violations) {
  const countByType = (type) => violations.filter((entry) => entry.type === type).length;
  return {
    totalViolations: violations.length,
    missingProductMappings: countByType('product-mapping-missing'),
    missingCoproductMappings: countByType('coproduct-mapping-missing'),
    inputCoverageGaps:
      countByType('product-required-input-missing') + countByType('product-required-input-unknown'),
    variantCoverageGaps: countByType('coproduct-variant-missing'),
    ambiguousDtoKeys: countByType('ambiguous-dto-key'),
    missingEvidence: countByType('coproduct-evidence-missing'),
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
    '# Context Pack Product/Coproduct Validation Report',
    '',
    `- GeneratedAt: ${report.generatedAt}`,
    `- Status: ${report.status.toUpperCase()}`,
    `- Map: \`${report.mapPath}\``,
    `- Schema: \`${report.schemaPath}\``,
    `- Context pack files: ${report.scannedContextPackFiles}`,
    `- Context morphisms: ${report.contextMorphismCount}`,
    `- Product mappings: ${report.productMappingCount}`,
    `- Coproduct mappings: ${report.coproductMappingCount}`,
    `- Failure variant coverage: ${report.coveredFailureVariants}/${report.totalFailureVariants}`,
    `- Violations: ${report.summary.totalViolations}`,
    '',
    '## Summary',
    `- missing product mappings: ${report.summary.missingProductMappings}`,
    `- missing coproduct mappings: ${report.summary.missingCoproductMappings}`,
    `- input coverage gaps: ${report.summary.inputCoverageGaps}`,
    `- variant coverage gaps: ${report.summary.variantCoverageGaps}`,
    `- ambiguous DTO keys: ${report.summary.ambiguousDtoKeys}`,
    `- missing evidence paths: ${report.summary.missingEvidence}`,
    '',
  ];

  if (report.violations.length === 0) {
    lines.push('## Violations', '', 'No violations detected.');
    return `${lines.join('\n')}\n`;
  }

  lines.push('## Violations', '', '| Type | Morphism | Rule | Message |', '| --- | --- | --- | --- |');
  for (const violation of report.violations) {
    lines.push(
      `| ${escapeMarkdownTableCell(violation.type)} | ${escapeMarkdownTableCell(violation.morphismId || '-')} | ${escapeMarkdownTableCell(violation.rule || '-')} | ${escapeMarkdownTableCell(violation.message)} |`,
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

function validateProductCoproduct(options) {
  const { resolvedPath: resolvedMapPath, data: mapPayload } = loadJsonFile(options.mapPath);
  const resolvedSchemaPath = path.resolve(options.schemaPath);
  const violations = [];
  violations.push(...validateMapSchema(mapPayload, resolvedSchemaPath));

  const sourcePatterns =
    options.contextPackSourcesOverride.length > 0
      ? options.contextPackSourcesOverride
      : Array.isArray(mapPayload.contextPackSources)
        ? mapPayload.contextPackSources
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

  const contextMorphisms = collectContextMorphisms(contextPackFiles, violations);
  const productStats = validateProducts(contextMorphisms, mapPayload.products, violations);
  const coproductStats = validateCoproducts(contextMorphisms, mapPayload.coproducts, violations);

  const report = {
    schemaVersion: 'context-pack-product-coproduct-report/v1',
    generatedAt: new Date().toISOString(),
    mapPath: toRelativePath(resolvedMapPath),
    schemaPath: toRelativePath(resolvedSchemaPath),
    contextPackSources: sourcePatterns,
    scannedContextPackFiles: contextPackFiles.length,
    contextMorphismCount: contextMorphisms.size,
    productMappingCount: productStats.productMappings.size,
    coproductMappingCount: Array.isArray(mapPayload.coproducts) ? mapPayload.coproducts.length : 0,
    totalFailureVariants: coproductStats.totalFailureVariants,
    coveredFailureVariants: coproductStats.coveredFailureVariants,
    uncoveredFailureVariants: Math.max(0, coproductStats.totalFailureVariants - coproductStats.coveredFailureVariants),
    summary: summarizeViolations(violations),
    status: violations.length === 0 ? 'pass' : 'fail',
    violations,
  };

  writeReport(report, options.reportJsonPath, options.reportMarkdownPath);
  process.stdout.write(`[context-pack:product-coproduct] report(json): ${toRelativePath(path.resolve(options.reportJsonPath))}\n`);
  process.stdout.write(`[context-pack:product-coproduct] report(md): ${toRelativePath(path.resolve(options.reportMarkdownPath))}\n`);

  if (report.status === 'fail') {
    process.stderr.write(`[context-pack:product-coproduct] validation failed (${violations.length} violation(s))\n`);
    return 2;
  }
  process.stdout.write(`[context-pack:product-coproduct] validation passed (${contextMorphisms.size} morphism(s))\n`);
  return 0;
}

try {
  const options = parseArgs(process.argv);
  if (options.help) {
    printHelp();
    process.exit(0);
  }
  process.exit(validateProductCoproduct(options));
} catch (error) {
  process.stderr.write(`[context-pack:product-coproduct] ${error instanceof Error ? error.message : String(error)}\n`);
  process.exit(1);
}
