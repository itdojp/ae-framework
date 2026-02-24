#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { globSync } from 'glob';
import yaml from 'yaml';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_SOURCES = ['spec/context-pack/**/*.{yml,yaml,json}'];
const DEFAULT_SCHEMA_PATH = 'schema/context-pack-v1.schema.json';
const DEFAULT_REPORT_JSON = 'artifacts/context-pack/context-pack-validate-report.json';
const DEFAULT_REPORT_MD = 'artifacts/context-pack/context-pack-validate-report.md';

const normalizePath = (value) => value.replace(/\\/g, '/');
const toRelativePath = (absolutePath) => normalizePath(path.relative(process.cwd(), absolutePath) || '.');

function printHelp() {
  process.stdout.write(`Context Pack v1 validator

Usage:
  node scripts/context-pack/validate.mjs [options]

Options:
  --sources <glob>      Source glob (repeatable, comma-separated supported)
  --schema <path>       JSON Schema path (default: ${DEFAULT_SCHEMA_PATH})
  --report-json <path>  JSON report path (default: ${DEFAULT_REPORT_JSON})
  --report-md <path>    Markdown report path (default: ${DEFAULT_REPORT_MD})
  --help, -h            Show this help
`);
}

function parseArgs(argv) {
  const options = {
    sources: [],
    schemaPath: DEFAULT_SCHEMA_PATH,
    reportJsonPath: DEFAULT_REPORT_JSON,
    reportMarkdownPath: DEFAULT_REPORT_MD,
    help: false,
  };

  const splitSourcePatterns = (rawValue) => {
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
  };

  const appendSources = (rawValue) => {
    for (const token of splitSourcePatterns(rawValue)) {
      const trimmed = token.trim();
      if (trimmed.length > 0) {
        options.sources.push(trimmed);
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
      appendSources(next);
      index += 1;
      continue;
    }
    if (arg.startsWith('--sources=')) {
      appendSources(arg.slice('--sources='.length));
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

function parseContextPackFile(sourcePath) {
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
    '',
    '## Source Patterns',
    ...report.sourcePatterns.map((pattern) => `- \`${pattern}\``),
    '',
  ];

  if (report.errors.length === 0) {
    lines.push('## Errors', '', 'No validation errors.');
    return `${lines.join('\n')}\n`;
  }

  lines.push('## Errors', '', '| File | Type | Path | Message |', '| --- | --- | --- | --- |');
  for (const error of report.errors) {
    const file = escapeMarkdownTableCell(error.file);
    const type = escapeMarkdownTableCell(error.type);
    const instancePath = escapeMarkdownTableCell(error.instancePath || '/');
    const message = escapeMarkdownTableCell(error.message);
    lines.push(
      `| ${file} | ${type} | ${instancePath} | ${message} |`
    );
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

function validateContextPacks(options) {
  const { schema, resolvedSchema } = loadSchema(options.schemaPath);
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);

  const sourceFiles = discoverSources(options.sources);
  const errors = [];
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
      payload = parseContextPackFile(sourcePath);
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
      payload.schemaVersion === 'context-pack-functor-map/v1'
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
    status: errors.length === 0 ? 'pass' : 'fail',
    errors,
  };

  writeReport(report, options.reportJsonPath, options.reportMarkdownPath);
  process.stdout.write(`[context-pack] report(json): ${toRelativePath(path.resolve(options.reportJsonPath))}\n`);
  process.stdout.write(`[context-pack] report(md): ${toRelativePath(path.resolve(options.reportMarkdownPath))}\n`);

  if (errors.length > 0) {
    process.stderr.write(`[context-pack] validation failed (${errors.length} error(s))\n`);
    return 2;
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
