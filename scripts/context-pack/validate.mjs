#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { globSync } from 'glob';
import yaml from 'yaml';

const DEFAULT_SOURCES = ['spec/context-pack/**/*.{yml,yaml,json}'];
const DEFAULT_SCHEMA_PATH = 'schema/context-pack-v1.schema.json';
const DEFAULT_REPORT_JSON = 'artifacts/context-pack/context-pack-validate-report.json';
const DEFAULT_REPORT_MD = 'artifacts/context-pack/context-pack-validate-report.md';
const NON_CONTEXT_PACK_SCHEMA_VERSIONS = new Set([
  'context-pack-boundary-map/v1',
  'context-pack-functor-map/v1',
  'context-pack-natural-transformation/v1',
  'context-pack-product-coproduct/v1',
  'context-pack-phase5-templates/v1',
]);
const DISCOVERY_SECTIONS = {
  goal_ids: 'goals',
  requirement_ids: 'requirements',
  business_use_case_ids: 'business_use_cases',
  decision_ids: 'decisions',
};

const normalizePath = (value) => value.replace(/\\/g, '/');
const toRelativePath = (absolutePath) => normalizePath(path.relative(process.cwd(), absolutePath) || '.');

function printHelp() {
  process.stdout.write(`Context Pack v1 validator

Usage:
  node scripts/context-pack/validate.mjs [options]

Options:
  --sources <glob>          Source glob (repeatable, comma-separated supported)
  --schema <path>           JSON Schema path (default: ${DEFAULT_SCHEMA_PATH})
  --report-json <path>      JSON report path (default: ${DEFAULT_REPORT_JSON})
  --report-md <path>        Markdown report path (default: ${DEFAULT_REPORT_MD})
  --discovery-pack <glob>   Discovery Pack source path/glob for upstream ref validation
  --help, -h                Show this help
`);
}

function splitSourcePatterns(rawValue) {
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
      chunks.push(buffer);
      buffer = '';
      continue;
    }
    buffer += char;
  }
  chunks.push(buffer);
  return chunks;
}

function parseArgs(argv) {
  const options = {
    sources: [],
    schemaPath: DEFAULT_SCHEMA_PATH,
    reportJsonPath: DEFAULT_REPORT_JSON,
    reportMarkdownPath: DEFAULT_REPORT_MD,
    discoveryPackSources: [],
    help: false,
  };

  const appendSources = (target, rawValue) => {
    for (const token of splitSourcePatterns(rawValue)) {
      const trimmed = token.trim();
      if (trimmed.length > 0) {
        target.push(trimmed);
      }
    }
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--sources') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --sources');
      }
      appendSources(options.sources, next);
      index += 1;
      continue;
    }
    if (arg.startsWith('--sources=')) {
      appendSources(options.sources, arg.slice('--sources='.length));
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
    if (arg === '--discovery-pack') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --discovery-pack');
      }
      appendSources(options.discoveryPackSources, next);
      index += 1;
      continue;
    }
    if (arg.startsWith('--discovery-pack=')) {
      appendSources(options.discoveryPackSources, arg.slice('--discovery-pack='.length));
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  if (options.sources.length === 0) {
    options.sources = [...DEFAULT_SOURCES];
  }

  return options;
}

function discoverSources(sourcePatterns) {
  const matches = new Set();
  for (const pattern of sourcePatterns) {
    for (const sourcePath of globSync(pattern, { nodir: true })) {
      matches.add(path.resolve(sourcePath));
    }
  }
  return Array.from(matches).sort((a, b) => a.localeCompare(b));
}

function loadSchema(schemaPath) {
  const resolvedSchema = path.resolve(schemaPath);
  const schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
  return { schema, resolvedSchema };
}

function parseStructuredFile(sourcePath) {
  const raw = fs.readFileSync(sourcePath, 'utf8');
  const lowerPath = sourcePath.toLowerCase();
  if (lowerPath.endsWith('.yaml') || lowerPath.endsWith('.yml')) {
    return yaml.parse(raw);
  }
  return JSON.parse(raw);
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
    '# Context Pack Validation Report',
    '',
    `- GeneratedAt: ${report.generatedAt}`,
    `- Status: ${report.status.toUpperCase()}`,
    `- Schema: \`${report.schemaPath}\``,
    `- Files scanned: ${report.scannedFiles}`,
    `- Valid files: ${report.validFiles}`,
    `- Invalid files: ${report.invalidFiles}`,
    `- Skipped files: ${report.skippedFiles}`,
    `- Warning count: ${report.warnings.length}`,
    '',
    '## Source Patterns',
    ...report.sourcePatterns.map((pattern) => `- \`${pattern}\``),
    '',
  ];

  lines.push('## Errors', '');
  if (report.errors.length === 0) {
    lines.push('No validation errors.', '');
  } else {
    lines.push('| File | Type | Path | Message |', '| --- | --- | --- | --- |');
    for (const error of report.errors) {
      const file = escapeMarkdownTableCell(error.file);
      const type = escapeMarkdownTableCell(error.type);
      const instancePath = escapeMarkdownTableCell(error.instancePath || '/');
      const message = escapeMarkdownTableCell(error.message);
      lines.push(`| ${file} | ${type} | ${instancePath} | ${message} |`);
    }
    lines.push('');
  }

  lines.push('## Warnings', '');
  if (report.warnings.length === 0) {
    lines.push('No validation warnings.', '');
  } else {
    lines.push('| File | Type | Path | Message |', '| --- | --- | --- | --- |');
    for (const warning of report.warnings) {
      const file = escapeMarkdownTableCell(warning.file);
      const type = escapeMarkdownTableCell(warning.type);
      const instancePath = escapeMarkdownTableCell(warning.instancePath || '/');
      const message = escapeMarkdownTableCell(warning.message);
      lines.push(`| ${file} | ${type} | ${instancePath} | ${message} |`);
    }
    lines.push('');
  }

  return `${lines.join('\n')}\n`;
}

function writeReport(report, jsonPath, markdownPath) {
  const resolvedJsonPath = path.resolve(jsonPath);
  const resolvedMarkdownPath = path.resolve(markdownPath);
  fs.mkdirSync(path.dirname(resolvedJsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(resolvedMarkdownPath), { recursive: true });
  fs.writeFileSync(resolvedJsonPath, `${JSON.stringify(report, null, 2)}\n`);
  fs.writeFileSync(resolvedMarkdownPath, buildMarkdownReport(report));
}

function buildDiscoveryIdIndex(payload) {
  const index = {
    goals: new Set(),
    requirements: new Set(),
    business_use_cases: new Set(),
    decisions: new Set(),
    approvedGoals: new Set(),
    approvedRequirements: new Set(),
    approvedBusinessUseCases: new Set(),
  };

  const register = (section, key) => {
    const entries = Array.isArray(payload?.[section]) ? payload[section] : [];
    for (const entry of entries) {
      const id = typeof entry?.id === 'string' ? entry.id.trim() : '';
      if (!id) {
        continue;
      }
      index[key].add(id);
      if (entry?.status === 'approved') {
        if (section === 'goals') index.approvedGoals.add(id);
        if (section === 'requirements') index.approvedRequirements.add(id);
        if (section === 'business_use_cases') index.approvedBusinessUseCases.add(id);
      }
    }
  };

  register('goals', 'goals');
  register('requirements', 'requirements');
  register('business_use_cases', 'business_use_cases');
  register('decisions', 'decisions');
  return index;
}

function hasAnyUpstreamRefs(payload) {
  const sections = ['morphisms', 'acceptance_tests', 'diagrams'];
  return sections.some((section) =>
    (Array.isArray(payload?.[section]) ? payload[section] : []).some((entry) => entry?.upstream_refs),
  );
}

function resolveDiscoveryPackCandidates(options, payload) {
  const candidates = [];
  for (const raw of options.discoveryPackSources) {
    candidates.push(raw);
  }
  const declaredPath = payload?.upstream?.discovery_pack?.path;
  if (typeof declaredPath === 'string' && declaredPath.trim()) {
    candidates.push(declaredPath.trim());
  }
  return Array.from(new Set(candidates));
}

function resolveDiscoveryPackFile(candidates) {
  const matches = new Set();
  for (const candidate of candidates) {
    if (candidate.includes('*') || candidate.includes('{')) {
      for (const file of globSync(candidate, { nodir: true })) {
        matches.add(path.resolve(file));
      }
      continue;
    }
    const resolvedCandidate = path.resolve(candidate);
    if (fs.existsSync(resolvedCandidate)) {
      matches.add(resolvedCandidate);
    }
  }
  return Array.from(matches).sort((a, b) => a.localeCompare(b));
}

function loadDiscoveryPack(resolvedPath, cache) {
  if (cache.has(resolvedPath)) {
    return cache.get(resolvedPath);
  }
  const payload = parseStructuredFile(resolvedPath);
  const loaded = {
    payload,
    index: buildDiscoveryIdIndex(payload),
  };
  cache.set(resolvedPath, loaded);
  return loaded;
}

function pushProblem(list, problem) {
  list.push(problem);
}

function collectUpstreamIds(upstreamRefs) {
  if (!upstreamRefs || typeof upstreamRefs !== 'object') {
    return [];
  }
  const entries = [];
  for (const [field, section] of Object.entries(DISCOVERY_SECTIONS)) {
    const ids = Array.isArray(upstreamRefs[field]) ? upstreamRefs[field] : [];
    for (const id of ids) {
      if (typeof id === 'string' && id.trim()) {
        entries.push({ field, section, id: id.trim() });
      }
    }
  }
  return entries;
}

function validateContextPackUpstream(payload, relativePath, options, errors, warnings, discoveryPackCache) {
  const hasUpstreamConfig = Boolean(payload?.upstream?.discovery_pack);
  const shouldValidateUpstream = hasUpstreamConfig || hasAnyUpstreamRefs(payload) || options.discoveryPackSources.length > 0;
  if (!shouldValidateUpstream) {
    return;
  }

  const candidates = resolveDiscoveryPackCandidates(options, payload);
  if (candidates.length === 0) {
    pushProblem(errors, {
      file: relativePath,
      type: 'discovery-pack-source-missing',
      instancePath: '/upstream/discovery_pack',
      schemaPath: '',
      keyword: 'upstream',
      message: 'Context Pack uses discovery upstream refs but no Discovery Pack source was provided',
    });
    return;
  }

  const matches = resolveDiscoveryPackFile(candidates);
  if (matches.length === 0) {
    pushProblem(errors, {
      file: relativePath,
      type: 'discovery-pack-source-missing',
      instancePath: '/upstream/discovery_pack/path',
      schemaPath: '',
      keyword: 'upstream',
      message: `No Discovery Pack files matched: ${candidates.join(', ')}`,
    });
    return;
  }
  if (matches.length !== 1) {
    pushProblem(errors, {
      file: relativePath,
      type: 'discovery-pack-source-ambiguous',
      instancePath: '/upstream/discovery_pack/path',
      schemaPath: '',
      keyword: 'upstream',
      message: `Expected exactly one Discovery Pack source, matched ${matches.length}`,
    });
    return;
  }

  let discoveryPayload;
  let discoveryIds;
  try {
    const loaded = loadDiscoveryPack(matches[0], discoveryPackCache);
    discoveryPayload = loaded.payload;
    discoveryIds = loaded.index;
  } catch (error) {
    pushProblem(errors, {
      file: relativePath,
      type: 'discovery-pack-parse',
      instancePath: '/upstream/discovery_pack/path',
      schemaPath: '',
      keyword: 'parse',
      message: error instanceof Error ? error.message : String(error),
    });
    return;
  }

  const referenced = {
    goals: new Set(),
    requirements: new Set(),
    business_use_cases: new Set(),
    decisions: new Set(),
  };

  const enforceRefs = (sectionName, entries, requireRefs) => {
    entries.forEach((entry, index) => {
      const instancePathBase = `/${sectionName}/${index}`;
      const entryId = typeof entry?.id === 'string' ? entry.id : `${sectionName}[${index}]`;
      const upstreamRefs = entry?.upstream_refs;
      if (requireRefs && (!upstreamRefs || typeof upstreamRefs !== 'object')) {
        pushProblem(warnings, {
          file: relativePath,
          type: 'upstream-refs-missing',
          instancePath: `${instancePathBase}/upstream_refs`,
          schemaPath: '',
          keyword: 'upstream_refs',
          message: `${entryId} is missing upstream_refs`,
        });
        return;
      }
      for (const ref of collectUpstreamIds(upstreamRefs)) {
        referenced[ref.section].add(ref.id);
        if (!discoveryIds[ref.section].has(ref.id)) {
          pushProblem(errors, {
            file: relativePath,
            type: 'upstream-ref-missing',
            instancePath: `${instancePathBase}/upstream_refs/${ref.field}`,
            schemaPath: '',
            keyword: 'upstream_refs',
            message: `${entryId} references unknown Discovery Pack ID ${ref.id}`,
          });
        }
      }
    });
  };

  enforceRefs('morphisms', Array.isArray(payload?.morphisms) ? payload.morphisms : [], true);
  enforceRefs('acceptance_tests', Array.isArray(payload?.acceptance_tests) ? payload.acceptance_tests : [], true);
  enforceRefs('diagrams', Array.isArray(payload?.diagrams) ? payload.diagrams : [], false);

  for (const id of discoveryIds.approvedRequirements) {
    if (!referenced.requirements.has(id)) {
      pushProblem(warnings, {
        file: relativePath,
        type: 'unmapped-approved-requirement',
        instancePath: '/morphisms',
        schemaPath: '',
        keyword: 'upstream_refs',
        message: `Approved Discovery requirement ${id} is not mapped from any Context Pack morphism/acceptance test/diagram`,
      });
    }
  }
  for (const id of discoveryIds.approvedBusinessUseCases) {
    if (!referenced.business_use_cases.has(id)) {
      pushProblem(warnings, {
        file: relativePath,
        type: 'unmapped-approved-business-use-case',
        instancePath: '/morphisms',
        schemaPath: '',
        keyword: 'upstream_refs',
        message: `Approved Discovery business use case ${id} is not mapped from any Context Pack element`,
      });
    }
  }
  if (hasUpstreamConfig) {
    const declaredProfile = payload.upstream.discovery_pack.profile;
    if (typeof declaredProfile === 'string' && declaredProfile.trim() && declaredProfile !== discoveryPayload?.profile) {
      pushProblem(warnings, {
        file: relativePath,
        type: 'discovery-pack-profile-mismatch',
        instancePath: '/upstream/discovery_pack/profile',
        schemaPath: '',
        keyword: 'profile',
        message: `Declared discovery profile ${declaredProfile} does not match source profile ${discoveryPayload?.profile ?? '(missing)'}`,
      });
    }
  }
}

function validateContextPacks(options) {
  const { schema, resolvedSchema } = loadSchema(options.schemaPath);
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);

  const sourceFiles = discoverSources(options.sources);
  const errors = [];
  const warnings = [];
  const discoveryPackCache = new Map();
  let validFiles = 0;
  let skippedFiles = 0;

  if (sourceFiles.length === 0) {
    errors.push({
      file: '(none)',
      type: 'sources',
      instancePath: '/',
      schemaPath: '',
      keyword: 'sources',
      message: `No context-pack files matched source patterns: ${options.sources.join(', ')}`,
    });
  }

  for (const sourcePath of sourceFiles) {
    const relativePath = toRelativePath(sourcePath);
    let payload;
    try {
      payload = parseStructuredFile(sourcePath);
    } catch (error) {
      errors.push({
        file: relativePath,
        type: 'parse',
        instancePath: '/',
        schemaPath: '',
        keyword: 'parse',
        message: error instanceof Error ? error.message : String(error),
      });
      continue;
    }

    if (
      payload &&
      typeof payload === 'object' &&
      typeof payload.schemaVersion === 'string' &&
      NON_CONTEXT_PACK_SCHEMA_VERSIONS.has(payload.schemaVersion)
    ) {
      skippedFiles += 1;
      continue;
    }

    if (!validate(payload)) {
      for (const validationError of validate.errors ?? []) {
        errors.push({
          file: relativePath,
          type: 'schema',
          instancePath: validationError.instancePath || '/',
          schemaPath: validationError.schemaPath,
          keyword: validationError.keyword,
          message: validationError.message ?? 'schema validation failed',
        });
      }
      continue;
    }

    validFiles += 1;
    validateContextPackUpstream(payload, relativePath, options, errors, warnings, discoveryPackCache);
  }

  const report = {
    schemaVersion: 'context-pack-validation-report/v1',
    generatedAt: new Date().toISOString(),
    schemaPath: toRelativePath(resolvedSchema),
    sourcePatterns: options.sources,
    scannedFiles: sourceFiles.length,
    validFiles,
    invalidFiles: sourceFiles.length - validFiles - skippedFiles,
    skippedFiles,
    status: errors.length > 0 ? 'fail' : warnings.length > 0 ? 'warn' : 'pass',
    errors,
    warnings,
  };

  writeReport(report, options.reportJsonPath, options.reportMarkdownPath);
  process.stdout.write(`[context-pack] report(json): ${toRelativePath(path.resolve(options.reportJsonPath))}\n`);
  process.stdout.write(`[context-pack] report(md): ${toRelativePath(path.resolve(options.reportMarkdownPath))}\n`);

  if (errors.length > 0) {
    process.stderr.write(`[context-pack] validation failed (${errors.length} error(s))\n`);
    return 2;
  }
  if (warnings.length > 0) {
    process.stdout.write(`[context-pack] validation completed with warnings (${warnings.length} warning(s))\n`);
    return 0;
  }
  process.stdout.write(`[context-pack] validation passed (${validFiles} file(s))\n`);
  return 0;
}

try {
  const options = parseArgs(process.argv);
  if (options.help) {
    printHelp();
    process.exit(0);
  }
  process.exit(validateContextPacks(options));
} catch (error) {
  process.stderr.write(`[context-pack] ${error instanceof Error ? error.message : String(error)}\n`);
  process.exit(1);
}
