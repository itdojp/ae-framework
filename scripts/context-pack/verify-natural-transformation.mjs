#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { globSync } from 'glob';
import yaml from 'yaml';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_MAP_PATH = 'spec/context-pack/natural-transformations.json';
const DEFAULT_SCHEMA_PATH = 'schema/context-pack-natural-transformation.schema.json';
const DEFAULT_REPORT_JSON = 'artifacts/context-pack/context-pack-natural-transformation-report.json';
const DEFAULT_REPORT_MD = 'artifacts/context-pack/context-pack-natural-transformation-report.md';
const ROOT_DIR = path.resolve(process.cwd());

const REQUIRED_CHECKS_BY_CHANGE_TYPE = {
  refactor: ['regression', 'compatibility'],
  migration: ['regression', 'compatibility', 'differential'],
  breaking: ['regression', 'differential'],
};

const normalizePath = (value) => value.replace(/\\/g, '/');
const toRelativePath = (absolutePath) => normalizePath(path.relative(process.cwd(), absolutePath) || '.');

function printHelp() {
  process.stdout.write(`Context Pack Natural Transformation validator

Usage:
  node scripts/context-pack/verify-natural-transformation.mjs [options]

Options:
  --map <path>                  Natural transformation map path (default: ${DEFAULT_MAP_PATH})
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

function validateNaturalTransformationMap(mapPayload, schemaPath) {
  const schemaRaw = fs.readFileSync(schemaPath, 'utf8');
  const schema = JSON.parse(schemaRaw);
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const valid = validate(mapPayload);
  if (valid) {
    return [];
  }
  return (validate.errors ?? []).map((error) => ({
    type: 'natural-transformation-schema-invalid',
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

function collectContextPackMetadata(contextPackFiles, violations) {
  const morphismIds = new Set();
  const diagramIds = new Set();
  const acceptanceTestIds = new Set();
  const forbiddenChanges = new Set();

  for (const filePath of contextPackFiles) {
    try {
      const payload = parseContextPackFile(filePath);
      if (!payload || typeof payload !== 'object' || isAuxiliaryContextPackPayload(payload)) {
        continue;
      }

      for (const id of toUniqueIds(payload.morphisms)) {
        morphismIds.add(id);
      }
      for (const id of toUniqueIds(payload.diagrams)) {
        diagramIds.add(id);
      }
      for (const id of toUniqueIds(payload.acceptance_tests)) {
        acceptanceTestIds.add(id);
      }
      for (const value of toStringArray(payload.forbidden_changes)) {
        forbiddenChanges.add(value);
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

  return {
    morphismIds,
    diagramIds,
    acceptanceTestIds,
    forbiddenChanges,
  };
}

function escapeRegexLiteral(value) {
  return value
    .replace(/\\/g, '\\\\')
    .replace(/[.*+?^${}()|[\]]/g, '\\$&');
}

function hasEntrypointSymbol(content, symbol) {
  const escapedSymbol = escapeRegexLiteral(symbol);
  const declarationPatterns = [
    new RegExp(`\\b(?:export\\s+)?(?:async\\s+)?function\\s+${escapedSymbol}\\b`),
    new RegExp(`\\b(?:export\\s+)?class\\s+${escapedSymbol}\\b`),
    new RegExp(`\\b(?:export\\s+)?(?:const|let|var|type|interface|enum)\\s+${escapedSymbol}\\b`),
    new RegExp(
      `(?:^|\\n)\\s*(?:(?:public|private|protected|static|readonly|abstract|override|async|get|set)\\s+)*${escapedSymbol}\\s*\\([^)]*\\)\\s*(?::\\s*[^\\n{]+)?\\s*\\{`,
    ),
    new RegExp(`\\bexport\\s*\\{[^}]*\\b${escapedSymbol}\\b[^}]*\\}`),
  ];
  return declarationPatterns.some((pattern) => pattern.test(content));
}

function hasGlobPattern(value) {
  return /[*?\[\]{}!]/.test(value);
}

function resolveEvidenceTargets(value) {
  if (hasGlobPattern(value)) {
    return globSync(value, {
      nodir: true,
      absolute: true,
      ignore: ['**/node_modules/**', '**/.git/**'],
    });
  }
  const resolved = path.resolve(value);
  if (!fs.existsSync(resolved) || !fs.statSync(resolved).isFile()) {
    return [];
  }
  return [resolved];
}

function verifyTransformationReferences(transformation, contextMetadata, violations) {
  const stages = [
    { key: 'before', value: transformation.before },
    { key: 'after', value: transformation.after },
  ];
  const checks = [
    { key: 'morphismIds', kind: 'morphism', values: contextMetadata.morphismIds },
    { key: 'diagramIds', kind: 'diagram', values: contextMetadata.diagramIds },
    { key: 'acceptanceTestIds', kind: 'acceptance_test', values: contextMetadata.acceptanceTestIds },
  ];

  for (const stage of stages) {
    const section = stage.value && typeof stage.value === 'object' ? stage.value : {};
    for (const check of checks) {
      for (const id of toStringArray(section[check.key])) {
        if (!check.values.has(id)) {
          violations.push({
            type: 'transformation-reference-missing',
            severity: 'error',
            transformationId: transformation.id,
            message: `Unknown ${check.kind} ID '${id}' in ${stage.key}.${check.key} (${transformation.id})`,
          });
        }
      }
    }
  }
}

function verifyCommutativityChecks(transformation, violations) {
  const checks =
    transformation.commutativityChecks && typeof transformation.commutativityChecks === 'object'
      ? transformation.commutativityChecks
      : {};
  const requiredChecks = REQUIRED_CHECKS_BY_CHANGE_TYPE[transformation.changeType] ?? [];
  let checkedEvidencePatterns = 0;

  for (const checkType of requiredChecks) {
    const values = toStringArray(checks[checkType]);
    if (values.length === 0) {
      violations.push({
        type: 'commutativity-check-missing',
        severity: 'error',
        transformationId: transformation.id,
        rule: `${transformation.changeType}:${checkType}`,
        message: `Required commutativity check '${checkType}' is missing for ${transformation.changeType} transformation '${transformation.id}'`,
      });
    }
  }

  for (const [checkType, value] of Object.entries(checks)) {
    for (const evidencePattern of toStringArray(value)) {
      checkedEvidencePatterns += 1;
      const matches = resolveEvidenceTargets(evidencePattern);
      if (matches.length === 0) {
        violations.push({
          type: 'commutativity-evidence-missing',
          severity: 'error',
          transformationId: transformation.id,
          rule: checkType,
          message: `Evidence path not found for '${checkType}': ${evidencePattern}`,
        });
      }
    }
  }

  return { checkedEvidencePatterns };
}

function verifyForbiddenChangeLinks(transformation, contextMetadata, violations) {
  const linkedForbiddenChanges = toStringArray(transformation.forbiddenChanges);
  if (transformation.changeType === 'breaking' && linkedForbiddenChanges.length === 0) {
    violations.push({
      type: 'forbidden-change-link-missing',
      severity: 'error',
      transformationId: transformation.id,
      message: `Breaking transformation '${transformation.id}' must link at least one forbidden change`,
    });
  }

  for (const forbiddenChange of linkedForbiddenChanges) {
    if (!contextMetadata.forbiddenChanges.has(forbiddenChange)) {
      violations.push({
        type: 'forbidden-change-mismatch',
        severity: 'error',
        transformationId: transformation.id,
        message: `forbiddenChanges entry was not found in context-pack forbidden_changes: '${forbiddenChange}'`,
      });
    }
  }
}

function verifyEntrypoints(transformation, violations) {
  const entrypoints = Array.isArray(transformation.entrypoints) ? transformation.entrypoints : [];
  let checkedEntrypoints = 0;
  for (const entrypoint of entrypoints) {
    if (!entrypoint || typeof entrypoint !== 'object' || typeof entrypoint.file !== 'string') {
      continue;
    }
    checkedEntrypoints += 1;
    const resolvedFilePath = path.resolve(entrypoint.file);
    if (!fs.existsSync(resolvedFilePath)) {
      violations.push({
        type: 'transformation-entrypoint-missing-file',
        severity: 'error',
        transformationId: transformation.id,
        file: toRelativePath(resolvedFilePath),
        message: `Entrypoint file not found for transformation '${transformation.id}': ${entrypoint.file}`,
      });
      continue;
    }
    if (typeof entrypoint.symbol === 'string' && entrypoint.symbol.trim().length > 0) {
      const content = fs.readFileSync(resolvedFilePath, 'utf8');
      if (!hasEntrypointSymbol(content, entrypoint.symbol)) {
        violations.push({
          type: 'transformation-entrypoint-missing-symbol',
          severity: 'error',
          transformationId: transformation.id,
          file: toRelativePath(resolvedFilePath),
          message: `Symbol '${entrypoint.symbol}' was not found in ${entrypoint.file}`,
        });
      }
    }
  }
  return { checkedEntrypoints };
}

function summarizeViolations(violations) {
  const countByType = (type) => violations.filter((entry) => entry.type === type).length;
  return {
    totalViolations: violations.length,
    missingReferences: countByType('transformation-reference-missing'),
    missingCommutativity: countByType('commutativity-check-missing'),
    missingEvidence: countByType('commutativity-evidence-missing'),
    forbiddenChangeViolations:
      countByType('forbidden-change-link-missing') + countByType('forbidden-change-mismatch'),
    missingEntrypoints:
      countByType('transformation-entrypoint-missing-file') +
      countByType('transformation-entrypoint-missing-symbol'),
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
    '# Context Pack Natural Transformation Report',
    '',
    `- GeneratedAt: ${report.generatedAt}`,
    `- Status: ${report.status.toUpperCase()}`,
    `- Map: \`${report.mapPath}\``,
    `- Schema: \`${report.schemaPath}\``,
    `- Context pack files: ${report.scannedContextPackFiles}`,
    `- Transformations: ${report.checkedTransformations}`,
    `- Violations: ${report.summary.totalViolations}`,
    '',
    '## Summary',
    `- missing references: ${report.summary.missingReferences}`,
    `- missing commutativity checks: ${report.summary.missingCommutativity}`,
    `- missing evidence: ${report.summary.missingEvidence}`,
    `- forbidden change link violations: ${report.summary.forbiddenChangeViolations}`,
    `- missing entrypoints: ${report.summary.missingEntrypoints}`,
    '',
  ];

  if (report.violations.length === 0) {
    lines.push('## Violations', '', 'No violations detected.');
    return `${lines.join('\n')}\n`;
  }

  lines.push('## Violations', '', '| Type | Transformation | File | Rule | Message |', '| --- | --- | --- | --- | --- |');
  for (const violation of report.violations) {
    lines.push(
      `| ${escapeMarkdownTableCell(violation.type)} | ${escapeMarkdownTableCell(violation.transformationId || '-')} | ${escapeMarkdownTableCell(violation.file || '-')} | ${escapeMarkdownTableCell(violation.rule || '-')} | ${escapeMarkdownTableCell(violation.message)} |`,
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

function validateNaturalTransformation(options) {
  const { resolvedPath: resolvedMapPath, data: mapPayload } = loadJsonFile(options.mapPath);
  const resolvedSchemaPath = path.resolve(options.schemaPath);

  const violations = [];
  const schemaViolations = validateNaturalTransformationMap(mapPayload, resolvedSchemaPath);
  violations.push(...schemaViolations);

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

  const contextMetadata = collectContextPackMetadata(contextPackFiles, violations);
  const transformations = Array.isArray(mapPayload.transformations) ? mapPayload.transformations : [];

  let checkedEntrypoints = 0;
  let checkedEvidencePatterns = 0;

  for (const transformation of transformations) {
    if (!transformation || typeof transformation !== 'object') {
      continue;
    }
    verifyTransformationReferences(transformation, contextMetadata, violations);
    verifyForbiddenChangeLinks(transformation, contextMetadata, violations);

    const commutativityStats = verifyCommutativityChecks(transformation, violations);
    checkedEvidencePatterns += commutativityStats.checkedEvidencePatterns;

    const entrypointStats = verifyEntrypoints(transformation, violations);
    checkedEntrypoints += entrypointStats.checkedEntrypoints;
  }

  const report = {
    schemaVersion: 'context-pack-natural-transformation-report/v1',
    generatedAt: new Date().toISOString(),
    mapPath: toRelativePath(resolvedMapPath),
    schemaPath: toRelativePath(resolvedSchemaPath),
    contextPackSources: sourcePatterns,
    scannedContextPackFiles: contextPackFiles.length,
    contextPackMorphismCount: contextMetadata.morphismIds.size,
    contextPackDiagramCount: contextMetadata.diagramIds.size,
    contextPackAcceptanceTestCount: contextMetadata.acceptanceTestIds.size,
    contextPackForbiddenChangeCount: contextMetadata.forbiddenChanges.size,
    checkedTransformations: transformations.length,
    checkedEntrypoints,
    checkedEvidencePatterns,
    summary: summarizeViolations(violations),
    status: violations.length === 0 ? 'pass' : 'fail',
    violations,
  };

  writeReport(report, options.reportJsonPath, options.reportMarkdownPath);
  process.stdout.write(
    `[context-pack:natural-transformation] report(json): ${toRelativePath(path.resolve(options.reportJsonPath))}\n`,
  );
  process.stdout.write(
    `[context-pack:natural-transformation] report(md): ${toRelativePath(path.resolve(options.reportMarkdownPath))}\n`,
  );

  if (report.status === 'fail') {
    process.stderr.write(
      `[context-pack:natural-transformation] validation failed (${violations.length} violation(s))\n`,
    );
    return 2;
  }
  process.stdout.write(
    `[context-pack:natural-transformation] validation passed (${transformations.length} transformation(s))\n`,
  );
  return 0;
}

try {
  const options = parseArgs(process.argv);
  if (options.help) {
    printHelp();
    process.exit(0);
  }
  process.exit(validateNaturalTransformation(options));
} catch (error) {
  process.stderr.write(
    `[context-pack:natural-transformation] ${error instanceof Error ? error.message : String(error)}\n`,
  );
  process.exit(1);
}
