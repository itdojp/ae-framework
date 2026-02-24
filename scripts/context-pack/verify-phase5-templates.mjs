#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { globSync } from 'glob';
import yaml from 'yaml';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_MAP_PATH = 'spec/context-pack/phase5-templates.json';
const DEFAULT_SCHEMA_PATH = 'schema/context-pack-phase5-templates.schema.json';
const DEFAULT_REPORT_JSON = 'artifacts/context-pack/context-pack-phase5-report.json';
const DEFAULT_REPORT_MD = 'artifacts/context-pack/context-pack-phase5-report.md';
const ROOT_DIR = path.resolve(process.cwd());

const normalizePath = (value) => value.replace(/\\/g, '/');
const toRelativePath = (absolutePath) => normalizePath(path.relative(process.cwd(), absolutePath) || '.');

function printHelp() {
  process.stdout.write(`Context Pack Phase5+ template validator

Usage:
  node scripts/context-pack/verify-phase5-templates.mjs [options]

Options:
  --map <path>                  Phase5+ template map path (default: ${DEFAULT_MAP_PATH})
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
    type: 'phase5-template-schema-invalid',
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

function resolveEvidenceTargets(value) {
  const hasGlobPattern = /[*?\[\]{}!]/.test(value);
  if (hasGlobPattern) {
    return globSync(value, {
      nodir: true,
      absolute: true,
      ignore: ['**/node_modules/**', '**/.git/**'],
    })
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

function collectContextMetadata(contextPackFiles, violations) {
  const metadata = {
    objectIds: new Set(),
    morphismIds: new Set(),
    diagramIds: new Set(),
  };

  for (const filePath of contextPackFiles) {
    try {
      const payload = parseContextPackFile(filePath);
      if (!payload || typeof payload !== 'object' || isAuxiliaryContextPackPayload(payload)) {
        continue;
      }
      for (const entry of Array.isArray(payload.objects) ? payload.objects : []) {
        if (entry && typeof entry === 'object' && typeof entry.id === 'string' && entry.id.trim().length > 0) {
          metadata.objectIds.add(entry.id.trim());
        }
      }
      for (const entry of Array.isArray(payload.morphisms) ? payload.morphisms : []) {
        if (entry && typeof entry === 'object' && typeof entry.id === 'string' && entry.id.trim().length > 0) {
          metadata.morphismIds.add(entry.id.trim());
        }
      }
      for (const entry of Array.isArray(payload.diagrams) ? payload.diagrams : []) {
        if (entry && typeof entry === 'object' && typeof entry.id === 'string' && entry.id.trim().length > 0) {
          metadata.diagramIds.add(entry.id.trim());
        }
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

  return metadata;
}

function toMapByTemplateId(entries, duplicateType, violations) {
  const mapping = new Map();
  for (const entry of entries) {
    if (!entry || typeof entry !== 'object' || typeof entry.id !== 'string') {
      continue;
    }
    const templateId = entry.id.trim();
    if (templateId.length === 0) {
      violations.push({
        type: 'phase5-template-id-empty',
        severity: 'error',
        message: 'Template id must include at least one non-whitespace character',
      });
      continue;
    }
    if (mapping.has(templateId)) {
      violations.push({
        type: duplicateType,
        severity: 'error',
        templateId,
        message: `Duplicate template id '${templateId}'`,
      });
      continue;
    }
    mapping.set(templateId, entry);
  }
  return mapping;
}

function validateReferenceId(referenceId, knownIds, violations, violationType, context) {
  const value = typeof referenceId === 'string' ? referenceId.trim() : '';
  if (!value) {
    return;
  }
  if (!knownIds.has(value)) {
    violations.push({
      type: violationType,
      severity: 'error',
      templateId: context.templateId,
      rule: context.rule,
      message: `${context.messagePrefix} '${value}' is not defined in context-pack`,
    });
  }
}

function validateReferenceArray(referenceValues, knownIds, violations, violationType, context) {
  for (const value of toStringArray(referenceValues)) {
    validateReferenceId(value, knownIds, violations, violationType, context);
  }
}

function validateEvidencePaths(evidencePaths, violations, context, counters) {
  for (const evidencePath of toStringArray(evidencePaths)) {
    counters.checkedEvidencePaths += 1;
    const matches = resolveEvidenceTargets(evidencePath);
    if (matches.length === 0) {
      violations.push({
        type: 'phase5-evidence-missing',
        severity: 'error',
        templateId: context.templateId,
        rule: context.rule,
        message: `Evidence path not found: ${evidencePath}`,
      });
      counters.missingEvidence += 1;
    }
  }
}

function validatePullbacks(metadata, pullbacks, violations) {
  const counters = {
    checkedTemplates: 0,
    checkedEvidencePaths: 0,
    missingEvidence: 0,
  };

  const templates = toMapByTemplateId(
    Array.isArray(pullbacks) ? pullbacks : [],
    'pullback-template-duplicate',
    violations,
  );

  for (const [templateId, template] of templates.entries()) {
    counters.checkedTemplates += 1;

    validateReferenceId(template.leftMorphismId, metadata.morphismIds, violations, 'pullback-morphism-missing', {
      templateId,
      rule: 'leftMorphismId',
      messagePrefix: 'Pullback left morphism',
    });
    validateReferenceId(template.rightMorphismId, metadata.morphismIds, violations, 'pullback-morphism-missing', {
      templateId,
      rule: 'rightMorphismId',
      messagePrefix: 'Pullback right morphism',
    });
    validateReferenceId(template.apexObjectId, metadata.objectIds, violations, 'pullback-object-missing', {
      templateId,
      rule: 'apexObjectId',
      messagePrefix: 'Pullback apex object',
    });
    validateReferenceArray(template.commutingDiagramIds, metadata.diagramIds, violations, 'pullback-diagram-missing', {
      templateId,
      rule: 'commutingDiagramIds',
      messagePrefix: 'Pullback commuting diagram',
    });

    validateEvidencePaths(template.evidencePaths, violations, { templateId, rule: 'evidencePaths' }, counters);
  }

  return counters;
}

function validatePushouts(metadata, pushouts, violations) {
  const counters = {
    checkedTemplates: 0,
    checkedEvidencePaths: 0,
    missingEvidence: 0,
  };

  const templates = toMapByTemplateId(
    Array.isArray(pushouts) ? pushouts : [],
    'pushout-template-duplicate',
    violations,
  );

  for (const [templateId, template] of templates.entries()) {
    counters.checkedTemplates += 1;

    validateReferenceId(template.leftMorphismId, metadata.morphismIds, violations, 'pushout-morphism-missing', {
      templateId,
      rule: 'leftMorphismId',
      messagePrefix: 'Pushout left morphism',
    });
    validateReferenceId(template.rightMorphismId, metadata.morphismIds, violations, 'pushout-morphism-missing', {
      templateId,
      rule: 'rightMorphismId',
      messagePrefix: 'Pushout right morphism',
    });
    validateReferenceId(template.coapexObjectId, metadata.objectIds, violations, 'pushout-object-missing', {
      templateId,
      rule: 'coapexObjectId',
      messagePrefix: 'Pushout coapex object',
    });
    validateReferenceArray(template.commutingDiagramIds, metadata.diagramIds, violations, 'pushout-diagram-missing', {
      templateId,
      rule: 'commutingDiagramIds',
      messagePrefix: 'Pushout commuting diagram',
    });

    validateEvidencePaths(template.evidencePaths, violations, { templateId, rule: 'evidencePaths' }, counters);
  }

  return counters;
}

function validateMonoidalFlows(metadata, monoidalFlows, violations) {
  const counters = {
    checkedTemplates: 0,
    checkedEvidencePaths: 0,
    missingEvidence: 0,
  };

  const templates = toMapByTemplateId(
    Array.isArray(monoidalFlows) ? monoidalFlows : [],
    'monoidal-template-duplicate',
    violations,
  );

  for (const [templateId, template] of templates.entries()) {
    counters.checkedTemplates += 1;

    const parallelMorphismIds = toStringArray(template.parallelMorphismIds);
    const parallelSet = new Set(parallelMorphismIds);
    if (parallelSet.size !== parallelMorphismIds.length) {
      violations.push({
        type: 'monoidal-parallel-morphism-duplicate',
        severity: 'error',
        templateId,
        rule: 'parallelMorphismIds',
        message: `Monoidal parallel morphism ids include duplicates for '${templateId}'`,
      });
    }

    validateReferenceArray(parallelMorphismIds, metadata.morphismIds, violations, 'monoidal-morphism-missing', {
      templateId,
      rule: 'parallelMorphismIds',
      messagePrefix: 'Monoidal parallel morphism',
    });
    validateReferenceId(template.mergeMorphismId, metadata.morphismIds, violations, 'monoidal-morphism-missing', {
      templateId,
      rule: 'mergeMorphismId',
      messagePrefix: 'Monoidal merge morphism',
    });

    for (const lawCheck of Array.isArray(template.tensorLawChecks) ? template.tensorLawChecks : []) {
      if (!lawCheck || typeof lawCheck !== 'object') {
        continue;
      }
      const ruleName = typeof lawCheck.name === 'string' && lawCheck.name.trim().length > 0
        ? `tensorLawChecks:${lawCheck.name.trim()}`
        : 'tensorLawChecks';
      validateEvidencePaths(lawCheck.evidencePaths, violations, { templateId, rule: ruleName }, counters);
    }
    validateEvidencePaths(template.stringDiagramPaths, violations, { templateId, rule: 'stringDiagramPaths' }, counters);
  }

  return counters;
}

function validateKleisliPipelines(metadata, kleisliPipelines, violations) {
  const counters = {
    checkedTemplates: 0,
    checkedEvidencePaths: 0,
    missingEvidence: 0,
    boundaryViolations: 0,
  };

  const templates = toMapByTemplateId(
    Array.isArray(kleisliPipelines) ? kleisliPipelines : [],
    'kleisli-template-duplicate',
    violations,
  );

  for (const [templateId, template] of templates.entries()) {
    counters.checkedTemplates += 1;

    const morphismIds = toStringArray(template.morphismIds);
    const morphismSet = new Set(morphismIds);
    if (morphismSet.size !== morphismIds.length) {
      violations.push({
        type: 'kleisli-morphism-duplicate',
        severity: 'error',
        templateId,
        rule: 'morphismIds',
        message: `Kleisli morphism ids include duplicates for '${templateId}'`,
      });
    }

    validateReferenceArray(morphismIds, metadata.morphismIds, violations, 'kleisli-morphism-missing', {
      templateId,
      rule: 'morphismIds',
      messagePrefix: 'Kleisli morphism',
    });

    const pureBoundary = toStringArray(template.pureBoundaryMorphismIds);
    const impureBoundary = toStringArray(template.impureBoundaryMorphismIds);
    const pureBoundarySet = new Set(pureBoundary);
    const impureBoundarySet = new Set(impureBoundary);

    for (const pureMorphismId of pureBoundarySet) {
      if (!morphismSet.has(pureMorphismId)) {
        counters.boundaryViolations += 1;
        violations.push({
          type: 'kleisli-boundary-reference-missing',
          severity: 'error',
          templateId,
          rule: 'pureBoundaryMorphismIds',
          message: `Pure boundary morphism '${pureMorphismId}' is not part of morphismIds for '${templateId}'`,
        });
      }
    }
    for (const impureMorphismId of impureBoundarySet) {
      if (!morphismSet.has(impureMorphismId)) {
        counters.boundaryViolations += 1;
        violations.push({
          type: 'kleisli-boundary-reference-missing',
          severity: 'error',
          templateId,
          rule: 'impureBoundaryMorphismIds',
          message: `Impure boundary morphism '${impureMorphismId}' is not part of morphismIds for '${templateId}'`,
        });
      }
    }
    for (const pureMorphismId of pureBoundarySet) {
      if (impureBoundarySet.has(pureMorphismId)) {
        counters.boundaryViolations += 1;
        violations.push({
          type: 'kleisli-boundary-overlap',
          severity: 'error',
          templateId,
          rule: pureMorphismId,
          message: `Morphism '${pureMorphismId}' is assigned to both pure and impure boundaries`,
        });
      }
    }
    if (impureBoundarySet.size === 0) {
      counters.boundaryViolations += 1;
      violations.push({
        type: 'kleisli-impure-boundary-missing',
        severity: 'error',
        templateId,
        rule: 'impureBoundaryMorphismIds',
        message: `Kleisli pipeline '${templateId}' requires at least one impure boundary morphism`,
      });
    }

    validateEvidencePaths(template.bindEvidencePaths, violations, { templateId, rule: 'bindEvidencePaths' }, counters);
    validateEvidencePaths(
      template.sideEffectEvidencePaths,
      violations,
      { templateId, rule: 'sideEffectEvidencePaths' },
      counters,
    );
  }

  return counters;
}

function summarizeViolations(violations, stats = {}) {
  const countByType = (type) => violations.filter((entry) => entry.type === type).length;
  const missingEvidence =
    Number.isFinite(stats.missingEvidence) && stats.missingEvidence >= 0
      ? stats.missingEvidence
      : countByType('phase5-evidence-missing');
  const boundaryViolations =
    Number.isFinite(stats.boundaryViolations) && stats.boundaryViolations >= 0
      ? stats.boundaryViolations
      : countByType('kleisli-boundary-overlap') +
        countByType('kleisli-boundary-reference-missing') +
        countByType('kleisli-impure-boundary-missing');

  return {
    totalViolations: violations.length,
    duplicateTemplates:
      countByType('pullback-template-duplicate') +
      countByType('pushout-template-duplicate') +
      countByType('monoidal-template-duplicate') +
      countByType('kleisli-template-duplicate'),
    missingMorphismReferences:
      countByType('pullback-morphism-missing') +
      countByType('pushout-morphism-missing') +
      countByType('monoidal-morphism-missing') +
      countByType('kleisli-morphism-missing'),
    missingObjectReferences: countByType('pullback-object-missing') + countByType('pushout-object-missing'),
    missingDiagramReferences: countByType('pullback-diagram-missing') + countByType('pushout-diagram-missing'),
    boundaryViolations,
    missingEvidence,
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
    '# Context Pack Phase5+ Template Validation Report',
    '',
    `- GeneratedAt: ${report.generatedAt}`,
    `- Status: ${report.status.toUpperCase()}`,
    `- Map: \`${report.mapPath}\``,
    `- Schema: \`${report.schemaPath}\``,
    `- Context pack files: ${report.scannedContextPackFiles}`,
    `- Pullback templates: ${report.checkedPullbacks}`,
    `- Pushout templates: ${report.checkedPushouts}`,
    `- Monoidal templates: ${report.checkedMonoidalFlows}`,
    `- Kleisli templates: ${report.checkedKleisliPipelines}`,
    `- Checked evidence paths: ${report.checkedEvidencePaths}`,
    `- Violations: ${report.summary.totalViolations}`,
    '',
    '## Summary',
    `- duplicate templates: ${report.summary.duplicateTemplates}`,
    `- missing morphism references: ${report.summary.missingMorphismReferences}`,
    `- missing object references: ${report.summary.missingObjectReferences}`,
    `- missing diagram references: ${report.summary.missingDiagramReferences}`,
    `- boundary violations: ${report.summary.boundaryViolations}`,
    `- missing evidence paths: ${report.summary.missingEvidence}`,
    '',
  ];

  if (report.violations.length === 0) {
    lines.push('## Violations', '', 'No violations detected.');
    return `${lines.join('\n')}\n`;
  }

  lines.push('## Violations', '', '| Type | Template | Rule | Message |', '| --- | --- | --- | --- |');
  for (const violation of report.violations) {
    lines.push(
      `| ${escapeMarkdownTableCell(violation.type)} | ${escapeMarkdownTableCell(violation.templateId || '-')} | ${escapeMarkdownTableCell(violation.rule || '-')} | ${escapeMarkdownTableCell(violation.message)} |`,
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

function validatePhase5Templates(options) {
  const { resolvedPath: resolvedMapPath, data: mapPayload } = loadJsonFile(options.mapPath);
  const resolvedSchemaPath = path.resolve(options.schemaPath);
  const violations = [];
  violations.push(...validateMapSchema(mapPayload, resolvedSchemaPath));
  const mapValue =
    mapPayload && typeof mapPayload === 'object' && !Array.isArray(mapPayload) ? mapPayload : {};

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

  const contextMetadata = collectContextMetadata(contextPackFiles, violations);
  const pullbackStats = validatePullbacks(contextMetadata, mapValue.pullbacks, violations);
  const pushoutStats = validatePushouts(contextMetadata, mapValue.pushouts, violations);
  const monoidalStats = validateMonoidalFlows(contextMetadata, mapValue.monoidalFlows, violations);
  const kleisliStats = validateKleisliPipelines(contextMetadata, mapValue.kleisliPipelines, violations);

  const checkedEvidencePaths =
    pullbackStats.checkedEvidencePaths +
    pushoutStats.checkedEvidencePaths +
    monoidalStats.checkedEvidencePaths +
    kleisliStats.checkedEvidencePaths;
  const missingEvidence =
    pullbackStats.missingEvidence +
    pushoutStats.missingEvidence +
    monoidalStats.missingEvidence +
    kleisliStats.missingEvidence;

  const report = {
    schemaVersion: 'context-pack-phase5-report/v1',
    generatedAt: new Date().toISOString(),
    mapPath: toRelativePath(resolvedMapPath),
    schemaPath: toRelativePath(resolvedSchemaPath),
    contextPackSources: sourcePatterns,
    scannedContextPackFiles: contextPackFiles.length,
    contextPackObjectCount: contextMetadata.objectIds.size,
    contextPackMorphismCount: contextMetadata.morphismIds.size,
    contextPackDiagramCount: contextMetadata.diagramIds.size,
    checkedPullbacks: pullbackStats.checkedTemplates,
    checkedPushouts: pushoutStats.checkedTemplates,
    checkedMonoidalFlows: monoidalStats.checkedTemplates,
    checkedKleisliPipelines: kleisliStats.checkedTemplates,
    checkedEvidencePaths,
    summary: summarizeViolations(violations, {
      missingEvidence,
      boundaryViolations: kleisliStats.boundaryViolations,
    }),
    status: violations.length === 0 ? 'pass' : 'fail',
    violations,
  };

  writeReport(report, options.reportJsonPath, options.reportMarkdownPath);
  process.stdout.write(`[context-pack:phase5] report(json): ${toRelativePath(path.resolve(options.reportJsonPath))}\n`);
  process.stdout.write(`[context-pack:phase5] report(md): ${toRelativePath(path.resolve(options.reportMarkdownPath))}\n`);

  if (report.status === 'fail') {
    process.stderr.write(`[context-pack:phase5] validation failed (${violations.length} violation(s))\n`);
    return 2;
  }
  process.stdout.write(`[context-pack:phase5] validation passed (${checkedEvidencePaths} evidence path(s) checked)\n`);
  return 0;
}

try {
  const options = parseArgs(process.argv);
  if (options.help) {
    printHelp();
    process.exit(0);
  }
  process.exit(validatePhase5Templates(options));
} catch (error) {
  process.stderr.write(`[context-pack:phase5] ${error instanceof Error ? error.message : String(error)}\n`);
  process.exit(1);
}
