#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { globSync } from 'glob';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_REPORT_DIR = 'artifacts/context-pack';
const DEFAULT_SCHEMA_PATH = 'schema/context-pack-suggestions.schema.json';
const DEFAULT_INPUT_REPORT_FILES = [
  'context-pack-validate-report.json',
  'context-pack-functor-report.json',
  'context-pack-natural-transformation-report.json',
  'context-pack-product-coproduct-report.json',
  'context-pack-phase5-report.json',
  'deps-summary.json',
];

const SOURCE_METADATA = {
  validate: {
    title: 'Base Schema',
    defaultFile: 'spec/context-pack',
    command: 'pnpm run context-pack:validate',
  },
  functor: {
    title: 'Functor',
    defaultFile: 'spec/context-pack/functor-map.json',
    command: 'pnpm run context-pack:verify-functor',
  },
  naturalTransformation: {
    title: 'Natural Transformation',
    defaultFile: 'spec/context-pack/natural-transformations.json',
    command: 'pnpm run context-pack:verify-natural-transformation',
  },
  productCoproduct: {
    title: 'Product/Coproduct',
    defaultFile: 'spec/context-pack/product-coproduct-map.json',
    command: 'pnpm run context-pack:verify-product-coproduct',
  },
  phase5: {
    title: 'Phase5+',
    defaultFile: 'spec/context-pack/phase5-templates.json',
    command: 'pnpm run context-pack:verify-phase5',
  },
  deps: {
    title: 'Dependency Boundary',
    defaultFile: 'configs/context-pack/dependency-rules.json',
    command: 'pnpm run context-pack:deps -- --strict=true',
  },
  unknown: {
    title: 'Unknown',
    defaultFile: 'spec/context-pack',
    command: 'pnpm run verify:lite',
  },
};

const CHANGE_TYPE_RULES = [
  { regex: /(^|-)unknown($|-)|(^|-)duplicate($|-)|(^|-)overlap($|-)/, changeType: 'remove' },
  { regex: /(^|-)missing($|-)|sources-empty|(^|-)parse-error($|-)|(^|-)check-missing($|-)/, changeType: 'add' },
  { regex: /layer-violation|forbidden|boundary-violation|dependency-cycle|(^|-)cycle($|-)/, changeType: 'investigate' },
];

const normalizePath = (value) => value.replace(/\\/g, '/');
const toRelativePath = (absolutePath) => normalizePath(path.relative(process.cwd(), absolutePath) || '.');

function printHelp() {
  process.stdout.write(`Context Pack suggestion generator

Usage:
  node scripts/context-pack/suggest.mjs [options]

Options:
  --report-dir <path>    Input report directory (default: ${DEFAULT_REPORT_DIR})
  --inputs <pattern>     Input report path/glob (repeatable, comma-separated)
  --schema <path>        Suggestions schema path (default: ${DEFAULT_SCHEMA_PATH})
  --report-json <path>   Output JSON path (default: <report-dir>/context-pack-suggestions.json)
  --report-md <path>     Output Markdown path (default: <report-dir>/context-pack-suggestions.md)
  --help, -h             Show this help
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
      const token = buffer.trim();
      if (token.length > 0) {
        chunks.push(token);
      }
      buffer = '';
      continue;
    }
    buffer += char;
  }
  const token = buffer.trim();
  if (token.length > 0) {
    chunks.push(token);
  }
  return chunks;
}

function parseArgs(argv) {
  const options = {
    reportDir: DEFAULT_REPORT_DIR,
    inputs: [],
    schemaPath: DEFAULT_SCHEMA_PATH,
    reportJsonPath: '',
    reportMarkdownPath: '',
    help: false,
  };

  const appendInputs = (rawValue) => {
    for (const pattern of splitPatterns(rawValue)) {
      options.inputs.push(pattern);
    }
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    if (arg === '--') {
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--report-dir') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --report-dir');
      }
      options.reportDir = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--report-dir=')) {
      options.reportDir = arg.slice('--report-dir='.length);
      continue;
    }
    if (arg === '--inputs') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --inputs');
      }
      appendInputs(next);
      index += 1;
      continue;
    }
    if (arg.startsWith('--inputs=')) {
      appendInputs(arg.slice('--inputs='.length));
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
    throw new Error(`unknown option: ${arg}`);
  }

  const reportDirResolved = path.resolve(options.reportDir);
  if (!options.reportJsonPath) {
    options.reportJsonPath = path.join(reportDirResolved, 'context-pack-suggestions.json');
  }
  if (!options.reportMarkdownPath) {
    options.reportMarkdownPath = path.join(reportDirResolved, 'context-pack-suggestions.md');
  }
  return options;
}

function inferSourceFromPayload(payload, fileName) {
  const schemaVersion = payload && typeof payload === 'object' ? String(payload.schemaVersion || '') : '';
  if (schemaVersion === 'context-pack-validation-report/v1') {
    return 'validate';
  }
  if (schemaVersion === 'context-pack-functor-report/v1') {
    return 'functor';
  }
  if (schemaVersion === 'context-pack-natural-transformation-report/v1') {
    return 'naturalTransformation';
  }
  if (schemaVersion === 'context-pack-product-coproduct-report/v1') {
    return 'productCoproduct';
  }
  if (schemaVersion === 'context-pack-phase5-report/v1') {
    return 'phase5';
  }
  if (schemaVersion === 'context-pack-deps-summary/v1') {
    return 'deps';
  }

  const normalizedFileName = String(fileName || '').toLowerCase();
  if (normalizedFileName.includes('validate-report')) {
    return 'validate';
  }
  if (normalizedFileName.includes('functor-report')) {
    return 'functor';
  }
  if (normalizedFileName.includes('natural-transformation-report')) {
    return 'naturalTransformation';
  }
  if (normalizedFileName.includes('product-coproduct-report')) {
    return 'productCoproduct';
  }
  if (normalizedFileName.includes('phase5-report')) {
    return 'phase5';
  }
  if (normalizedFileName.includes('deps-summary')) {
    return 'deps';
  }
  return 'unknown';
}

function resolveInputPaths(options) {
  if (options.inputs.length === 0) {
    return DEFAULT_INPUT_REPORT_FILES
      .map((fileName) => path.resolve(options.reportDir, fileName))
      .sort((left, right) => left.localeCompare(right));
  }

  const resolved = new Set();
  for (const token of options.inputs) {
    if (/[*?[\]{}!]/.test(token)) {
      const matches = globSync(token, { nodir: true, absolute: true });
      for (const match of matches) {
        resolved.add(path.resolve(match));
      }
      if (matches.length === 0) {
        resolved.add(path.resolve(token));
      }
    } else {
      resolved.add(path.resolve(token));
    }
  }
  return Array.from(resolved).sort((left, right) => left.localeCompare(right));
}

function sanitizeMessage(value) {
  return String(value || '')
    .replace(/\s+/g, ' ')
    .trim();
}

function normalizeSeverity(value, fallback = 'error') {
  const normalized = String(value || '').trim().toLowerCase();
  if (normalized === 'error' || normalized === 'warn' || normalized === 'warning' || normalized === 'info') {
    return normalized === 'warning' ? 'warn' : normalized;
  }
  return fallback;
}

function extractTargetId(entry) {
  const candidateKeys = [
    'targetId',
    'objectId',
    'morphismId',
    'transformationId',
    'templateId',
    'ruleId',
    'rule',
    'id',
  ];

  for (const key of candidateKeys) {
    const value = entry?.[key];
    if (typeof value === 'string' && value.trim().length > 0) {
      return value.trim();
    }
  }
  if (typeof entry?.from === 'string' && typeof entry?.to === 'string') {
    return `${entry.from.trim()} -> ${entry.to.trim()}`;
  }
  return null;
}

function deriveTargetFile(entry, sourceId) {
  if (entry && typeof entry.file === 'string') {
    const file = entry.file.trim();
    if (file.length > 0 && file !== '-' && file !== '(none)') {
      return normalizePath(file);
    }
  }
  if (
    sourceId === 'deps'
    && entry
    && typeof entry.from === 'string'
    && entry.from.trim().startsWith('src/')
  ) {
    return normalizePath(entry.from.trim());
  }
  const metadata = SOURCE_METADATA[sourceId] || SOURCE_METADATA.unknown;
  return metadata.defaultFile;
}

function deriveChangeType(violationType, sourceId) {
  if (sourceId === 'validate') {
    return 'update';
  }
  const normalizedType = String(violationType || '').toLowerCase();
  for (const rule of CHANGE_TYPE_RULES) {
    if (rule.regex.test(normalizedType)) {
      return rule.changeType;
    }
  }
  return 'update';
}

function deriveCommand(sourceId) {
  return (SOURCE_METADATA[sourceId] || SOURCE_METADATA.unknown).command;
}

function deriveRationale(entry, sourceId) {
  const sourceTitle = (SOURCE_METADATA[sourceId] || SOURCE_METADATA.unknown).title;
  const message = sanitizeMessage(entry?.message || entry?.reason || 'Context Pack violation detected.');
  if (!message) {
    return `${sourceTitle} validation requires context-pack update.`;
  }
  return `${sourceTitle}: ${message}`;
}

function normalizeViolationEntry(rawEntry, sourceId) {
  const type = String(rawEntry?.type || rawEntry?.keyword || 'unknown').trim() || 'unknown';
  return {
    sourceId,
    type,
    severity: normalizeSeverity(rawEntry?.severity),
    targetId: extractTargetId(rawEntry),
    file: deriveTargetFile(rawEntry, sourceId),
    changeType: deriveChangeType(type, sourceId),
    rationale: deriveRationale(rawEntry, sourceId),
    suggestedCommand: deriveCommand(sourceId),
  };
}

function buildSuggestionsFromPayload(sourceId, payload) {
  if (!payload || typeof payload !== 'object') {
    return [];
  }
  const result = [];

  if (sourceId === 'validate') {
    const errors = Array.isArray(payload.errors) ? payload.errors : [];
    for (const error of errors) {
      const entry = normalizeViolationEntry(error, sourceId);
      entry.violationType = String(error?.type || error?.keyword || 'validate-error');
      result.push(entry);
    }
    return result;
  }

  const violations = Array.isArray(payload.violations) ? payload.violations : [];
  for (const violation of violations) {
    const entry = normalizeViolationEntry(violation, sourceId);
    entry.violationType = String(violation?.type || 'unknown');
    result.push(entry);
  }
  return result;
}

function dedupeSuggestions(suggestions) {
  const seen = new Set();
  const deduped = [];
  for (const suggestion of suggestions) {
    const key = [
      suggestion.source,
      suggestion.file,
      suggestion.changeType,
      suggestion.targetId || '',
      suggestion.violationType,
      suggestion.rationale,
    ].join('|');
    if (seen.has(key)) {
      continue;
    }
    seen.add(key);
    deduped.push(suggestion);
  }
  return deduped;
}

function countBy(items, keySelector) {
  const counts = {};
  for (const item of items) {
    const key = keySelector(item);
    if (!key) {
      continue;
    }
    counts[key] = (counts[key] || 0) + 1;
  }
  return counts;
}

function escapeMarkdownCell(value) {
  return String(value ?? '')
    .replace(/\\/g, '\\\\')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/`/g, '\\`')
    .replace(/\|/g, '\\|')
    .replace(/\r?\n/g, '<br>');
}

function renderMarkdown(report) {
  const lines = [
    '# Context Pack Suggestions',
    '',
    `- GeneratedAt: ${report.generatedAt}`,
    `- Status: ${report.status.toUpperCase()}`,
    `- Scanned reports: ${report.summary.scannedReports}`,
    `- Loaded reports: ${report.summary.loadedReports}`,
    `- Missing reports: ${report.summary.missingReports}`,
    `- Suggested changes: ${report.summary.totalSuggestions}`,
    '',
    '## Source Reports',
    '',
    '| Source | Report | Loaded | Status | Violations |',
    '| --- | --- | --- | --- | ---: |',
  ];

  for (const source of report.sourceReports) {
    lines.push(
      `| ${escapeMarkdownCell(source.source)} | ${escapeMarkdownCell(source.path)} | ${source.loaded ? 'yes' : 'no'} | ${escapeMarkdownCell(source.status)} | ${Number(source.violationCount || 0)} |`,
    );
  }

  if (report.recommendedContextChanges.length === 0) {
    lines.push('', '## Recommended Context Changes', '', 'No suggestions generated.');
    return `${lines.join('\n')}\n`;
  }

  lines.push('', '## Recommended Context Changes', '');
  lines.push('| Source | File | Change | Target | Violation | Command | Rationale |');
  lines.push('| --- | --- | --- | --- | --- | --- | --- |');
  for (const item of report.recommendedContextChanges.slice(0, 100)) {
    lines.push(
      `| ${escapeMarkdownCell(item.source)} | ${escapeMarkdownCell(item.file)} | ${escapeMarkdownCell(item.changeType)} | ${escapeMarkdownCell(item.targetId || '-')} | ${escapeMarkdownCell(item.violationType)} | ${escapeMarkdownCell(item.suggestedCommand || '-')} | ${escapeMarkdownCell(item.rationale)} |`,
    );
  }
  return `${lines.join('\n')}\n`;
}

function validateOutputSchema(report, schemaPath) {
  const resolvedSchemaPath = path.resolve(schemaPath);
  const schema = JSON.parse(fs.readFileSync(resolvedSchemaPath, 'utf8'));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  if (!validate(report)) {
    const details = (validate.errors || [])
      .map((error) => `${error.instancePath || '/'} ${error.message || error.keyword}`)
      .join('; ');
    throw new Error(`suggestion output schema validation failed: ${details}`);
  }
  return toRelativePath(resolvedSchemaPath);
}

function writeOutputs(report, reportJsonPath, reportMarkdownPath) {
  const resolvedJsonPath = path.resolve(reportJsonPath);
  const resolvedMarkdownPath = path.resolve(reportMarkdownPath);
  fs.mkdirSync(path.dirname(resolvedJsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(resolvedMarkdownPath), { recursive: true });
  fs.writeFileSync(resolvedJsonPath, `${JSON.stringify(report, null, 2)}\n`);
  fs.writeFileSync(resolvedMarkdownPath, renderMarkdown(report));
  return {
    resolvedJsonPath,
    resolvedMarkdownPath,
  };
}

function main() {
  const options = parseArgs(process.argv);
  if (options.help) {
    printHelp();
    return 0;
  }

  const inputPaths = resolveInputPaths(options);
  const sourceReports = [];
  const rawSuggestions = [];

  for (const inputPath of inputPaths) {
    const reportPath = path.resolve(inputPath);
    const relativePath = toRelativePath(reportPath);
    if (!fs.existsSync(reportPath)) {
      sourceReports.push({
        source: inferSourceFromPayload(null, path.basename(reportPath)),
        path: relativePath,
        loaded: false,
        status: 'missing',
        violationCount: 0,
      });
      continue;
    }

    let payload;
    try {
      payload = JSON.parse(fs.readFileSync(reportPath, 'utf8'));
    } catch (error) {
      sourceReports.push({
        source: inferSourceFromPayload(null, path.basename(reportPath)),
        path: relativePath,
        loaded: false,
        status: 'parse_error',
        violationCount: 0,
      });
      rawSuggestions.push({
        source: 'unknown',
        sourceReport: relativePath,
        file: relativePath,
        changeType: 'update',
        targetId: null,
        violationType: 'report-parse-error',
        severity: 'error',
        rationale: sanitizeMessage(error instanceof Error ? error.message : String(error)),
        suggestedCommand: 'pnpm run verify:lite',
      });
      continue;
    }

    const sourceId = inferSourceFromPayload(payload, path.basename(reportPath));
    const sourceEntries = buildSuggestionsFromPayload(sourceId, payload);
    for (const suggestion of sourceEntries) {
      rawSuggestions.push({
        source: sourceId,
        sourceReport: relativePath,
        file: suggestion.file,
        changeType: suggestion.changeType,
        targetId: suggestion.targetId,
        violationType: suggestion.violationType,
        severity: suggestion.severity,
        rationale: suggestion.rationale,
        suggestedCommand: suggestion.suggestedCommand,
      });
    }

    sourceReports.push({
      source: sourceId,
      path: relativePath,
      loaded: true,
      status: typeof payload.status === 'string' && payload.status.trim().length > 0 ? payload.status : 'unknown',
      violationCount: sourceEntries.length,
    });
  }

  const recommendedContextChanges = dedupeSuggestions(rawSuggestions);
  const status = recommendedContextChanges.length === 0
    ? 'pass'
    : recommendedContextChanges.some((entry) => entry.severity === 'error')
      ? 'fail'
      : 'warn';

  const report = {
    schemaVersion: 'context-pack-suggestions/v1',
    generatedAt: new Date().toISOString(),
    reportDir: toRelativePath(path.resolve(options.reportDir)),
    status,
    sourceReports,
    summary: {
      scannedReports: inputPaths.length,
      loadedReports: sourceReports.filter((entry) => entry.loaded).length,
      missingReports: sourceReports.filter((entry) => !entry.loaded && entry.status === 'missing').length,
      totalSuggestions: recommendedContextChanges.length,
      bySource: countBy(recommendedContextChanges, (entry) => entry.source),
      byChangeType: countBy(recommendedContextChanges, (entry) => entry.changeType),
      byViolationType: countBy(recommendedContextChanges, (entry) => entry.violationType),
    },
    recommendedContextChanges,
  };

  const schemaPath = validateOutputSchema(report, options.schemaPath);
  report.schemaPath = schemaPath;

  const outputPaths = writeOutputs(report, options.reportJsonPath, options.reportMarkdownPath);
  process.stdout.write(`[context-pack:suggest] report(json): ${toRelativePath(outputPaths.resolvedJsonPath)}\n`);
  process.stdout.write(`[context-pack:suggest] report(md): ${toRelativePath(outputPaths.resolvedMarkdownPath)}\n`);
  process.stdout.write(`[context-pack:suggest] status=${report.status} suggestions=${report.summary.totalSuggestions}\n`);
  return 0;
}

try {
  process.exit(main());
} catch (error) {
  process.stderr.write(`[context-pack:suggest] ${error instanceof Error ? error.message : String(error)}\n`);
  process.exit(1);
}
