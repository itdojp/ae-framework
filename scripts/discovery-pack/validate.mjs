#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

import {
  DEFAULT_SOURCES,
  analyzeDiscoveryPackSemantics,
  discoverSources,
  parseYamlOrJson,
  splitSourcePatterns,
  toRelativePath,
} from './lib.mjs';

const DEFAULT_SCHEMA_PATH = 'schema/discovery-pack-v1.schema.json';
const DEFAULT_OUTPUT_DIR = 'artifacts/discovery-pack';
const DEFAULT_REPORT_JSON = 'discovery-pack-validate-report.json';
const DEFAULT_REPORT_MD = 'discovery-pack-validate-report.md';
const SUPPORTED_FORMATS = new Set(['json', 'md', 'both']);
const SUPPORTED_FAIL_ON = new Set([
  'blocking-open-questions',
  'orphan-approved-requirements',
  'orphan-approved-business-use-cases',
]);

const escapeMarkdownTableCell = (value) =>
  String(value ?? '')
    .replace(/\\/g, '\\\\')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/`/g, '\\`')
    .replace(/\|/g, '\\|')
    .replace(/\r?\n/g, '<br>');

function printHelp() {
  process.stdout.write(`Discovery Pack validator

Usage:
  node scripts/discovery-pack/validate.mjs [options]

Options:
  --sources <glob>        Source glob (repeatable, comma-separated supported)
  --schema <path>         JSON Schema path (default: ${DEFAULT_SCHEMA_PATH})
  --format <format>       json | md | both (default: both)
  --output-dir <dir>      Output directory (default: ${DEFAULT_OUTPUT_DIR})
  --strict-approved       Fail when approved elements depend on non-approved elements
  --fail-on <rule>        Repeatable, comma-separated supported:
                          blocking-open-questions
                          orphan-approved-requirements
                          orphan-approved-business-use-cases
  --help, -h              Show this help
`);
}

export function parseArgs(argv) {
  const options = {
    sources: [],
    schemaPath: DEFAULT_SCHEMA_PATH,
    format: 'both',
    outputDir: DEFAULT_OUTPUT_DIR,
    strictApproved: false,
    failOn: [],
    help: false,
  };

  const appendSources = (rawValue) => {
    for (const token of splitSourcePatterns(rawValue)) {
      const trimmed = token.trim();
      if (trimmed) {
        options.sources.push(trimmed);
      }
    }
  };

  const appendFailOn = (rawValue) => {
    for (const token of splitSourcePatterns(rawValue)) {
      const trimmed = token.trim();
      if (!trimmed) {
        continue;
      }
      if (!SUPPORTED_FAIL_ON.has(trimmed)) {
        throw Object.assign(new Error(`unsupported --fail-on value: ${trimmed}`), {
          exitCode: 2,
        });
      }
      if (!options.failOn.includes(trimmed)) {
        options.failOn.push(trimmed);
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
    if (arg === '--strict-approved') {
      options.strictApproved = true;
      continue;
    }
    if (arg === '--sources') {
      if (!next || next.startsWith('-')) {
        throw Object.assign(new Error('missing value for --sources'), { exitCode: 2 });
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
        throw Object.assign(new Error('missing value for --schema'), { exitCode: 2 });
      }
      options.schemaPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--schema=')) {
      options.schemaPath = arg.slice('--schema='.length);
      continue;
    }
    if (arg === '--format') {
      if (!next || next.startsWith('-')) {
        throw Object.assign(new Error('missing value for --format'), { exitCode: 2 });
      }
      options.format = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--format=')) {
      options.format = arg.slice('--format='.length);
      continue;
    }
    if (arg === '--output-dir') {
      if (!next || next.startsWith('-')) {
        throw Object.assign(new Error('missing value for --output-dir'), { exitCode: 2 });
      }
      options.outputDir = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--output-dir=')) {
      options.outputDir = arg.slice('--output-dir='.length);
      continue;
    }
    if (arg === '--fail-on') {
      if (!next || next.startsWith('-')) {
        throw Object.assign(new Error('missing value for --fail-on'), { exitCode: 2 });
      }
      appendFailOn(next);
      index += 1;
      continue;
    }
    if (arg.startsWith('--fail-on=')) {
      appendFailOn(arg.slice('--fail-on='.length));
      continue;
    }
    throw Object.assign(new Error(`unknown option: ${arg}`), { exitCode: 2 });
  }

  if (!SUPPORTED_FORMATS.has(options.format)) {
    throw Object.assign(new Error(`unsupported --format value: ${options.format}`), {
      exitCode: 2,
    });
  }

  if (options.sources.length === 0) {
    options.sources = [...DEFAULT_SOURCES];
  }

  return options;
}

const loadSchema = (schemaPath) => {
  const resolvedSchema = path.resolve(schemaPath);
  const schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
  return { schema, resolvedSchema };
};

const buildMarkdownReport = (report) => {
  const lines = [
    '# Discovery Pack Validation Report',
    '',
    `- GeneratedAt: ${report.generatedAt}`,
    `- Status: ${report.status.toUpperCase()}`,
    `- Schema: \`${report.schemaPath}\``,
    `- Files scanned: ${report.scannedFiles}`,
    `- Passed files: ${report.passedFiles}`,
    `- Warning files: ${report.warningFiles}`,
    `- Failed files: ${report.failedFiles}`,
    `- Strict approved: ${report.strictApproved}`,
    '',
    '## Source Patterns',
    ...report.sourcePatterns.map((pattern) => `- \`${pattern}\``),
    '',
    '## Summary',
    `- duplicate IDs: ${report.summary.duplicateIds}`,
    `- unresolved source refs: ${report.summary.unresolvedSourceRefs}`,
    `- unresolved trace refs: ${report.summary.unresolvedTraceRefs}`,
    `- approved -> rejected refs: ${report.summary.approvedDependsOnRejected}`,
    `- strict approved violations: ${report.summary.strictApprovedViolations}`,
    `- blocking open questions: ${report.summary.blockingOpenQuestions}`,
    `- orphan approved requirements: ${report.summary.orphanApprovedRequirements}`,
    `- orphan approved business use cases: ${report.summary.orphanApprovedBusinessUseCases}`,
    '',
  ];

  if (report.files.length > 0) {
    lines.push('## Files', '', '| File | Status | Errors | Warnings |', '| --- | --- | --- | --- |');
    for (const file of report.files) {
      lines.push(
        `| ${escapeMarkdownTableCell(file.file)} | ${escapeMarkdownTableCell(file.status)} | ${file.errors.length} | ${file.warnings.length} |`,
      );
    }
    lines.push('');
  }

  const allViolations = report.files.flatMap((file) =>
    [...file.errors, ...file.warnings].map((entry) => ({ file: file.file, ...entry })),
  );

  if (allViolations.length === 0) {
    lines.push('## Violations', '', 'No validation violations.');
    return `${lines.join('\n')}\n`;
  }

  lines.push('## Violations', '', '| File | Severity | Type | ID | Ref | Message |', '| --- | --- | --- | --- | --- | --- |');
  for (const violation of allViolations) {
    lines.push(
      `| ${escapeMarkdownTableCell(violation.file)} | ${escapeMarkdownTableCell(violation.severity)} | ${escapeMarkdownTableCell(violation.type)} | ${escapeMarkdownTableCell(violation.id ?? '')} | ${escapeMarkdownTableCell(violation.ref ?? '')} | ${escapeMarkdownTableCell(violation.message)} |`,
    );
  }

  return `${lines.join('\n')}\n`;
};

const writeReport = (report, format, outputDir) => {
  const resolvedOutputDir = path.resolve(outputDir);
  fs.mkdirSync(resolvedOutputDir, { recursive: true });

  let jsonPath = null;
  let markdownPath = null;

  if (format === 'json' || format === 'both') {
    jsonPath = path.join(resolvedOutputDir, DEFAULT_REPORT_JSON);
    fs.writeFileSync(jsonPath, `${JSON.stringify(report, null, 2)}\n`);
  }
  if (format === 'md' || format === 'both') {
    markdownPath = path.join(resolvedOutputDir, DEFAULT_REPORT_MD);
    fs.writeFileSync(markdownPath, buildMarkdownReport(report));
  }

  return { jsonPath, markdownPath };
};

const shouldFailOnWarnings = (summary, failOn) => {
  const failReasons = [];
  if (failOn.includes('blocking-open-questions') && summary.blockingOpenQuestions > 0) {
    failReasons.push('blocking-open-questions');
  }
  if (failOn.includes('orphan-approved-requirements') && summary.orphanApprovedRequirements > 0) {
    failReasons.push('orphan-approved-requirements');
  }
  if (
    failOn.includes('orphan-approved-business-use-cases') &&
    summary.orphanApprovedBusinessUseCases > 0
  ) {
    failReasons.push('orphan-approved-business-use-cases');
  }
  return failReasons;
};

export function validateDiscoveryPackSources(options) {
  const { schema, resolvedSchema } = loadSchema(options.schemaPath);
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const sourceFiles = discoverSources(options.sources);

  if (sourceFiles.length === 0) {
    process.stderr.write(
      `[discovery-pack] no discovery-pack files matched source patterns: ${options.sources.join(', ')}\n`,
    );
    return 2;
  }

  const fileReports = [];
  const aggregateSummary = {
    duplicateIds: 0,
    unresolvedSourceRefs: 0,
    unresolvedTraceRefs: 0,
    approvedDependsOnRejected: 0,
    strictApprovedViolations: 0,
    blockingOpenQuestions: 0,
    orphanApprovedRequirements: 0,
    orphanApprovedBusinessUseCases: 0,
  };

  for (const sourcePath of sourceFiles) {
    const relativePath = toRelativePath(sourcePath);
    const fileReport = {
      file: relativePath,
      status: 'pass',
      errors: [],
      warnings: [],
    };

    let payload;
    try {
      payload = parseYamlOrJson(sourcePath);
    } catch (error) {
      fileReport.errors.push({
        severity: 'error',
        type: 'parse',
        message: error instanceof Error ? error.message : String(error),
      });
      fileReport.status = 'fail';
      fileReports.push(fileReport);
      continue;
    }

    if (!validate(payload)) {
      for (const validationError of validate.errors ?? []) {
        fileReport.errors.push({
          severity: 'error',
          type: 'schema',
          ref: validationError.instancePath || '/',
          message: validationError.message ?? 'schema validation failed',
        });
      }
      fileReport.status = 'fail';
      fileReports.push(fileReport);
      continue;
    }

    const semantic = analyzeDiscoveryPackSemantics(payload, {
      strictApproved: options.strictApproved,
    });

    for (const error of semantic.errors) {
      fileReport.errors.push({ severity: 'error', ...error });
    }
    for (const warning of semantic.warnings) {
      fileReport.warnings.push({ severity: 'warn', ...warning });
    }

    for (const [key, value] of Object.entries(semantic.summary)) {
      aggregateSummary[key] += value;
    }

    if (fileReport.errors.length > 0) {
      fileReport.status = 'fail';
    } else if (fileReport.warnings.length > 0) {
      fileReport.status = 'warn';
    }
    fileReports.push(fileReport);
  }

  const failOnReasons = shouldFailOnWarnings(aggregateSummary, options.failOn);
  const passedFiles = fileReports.filter((entry) => entry.status === 'pass').length;
  const warningFiles = fileReports.filter((entry) => entry.status === 'warn').length;
  const failedFiles = fileReports.filter((entry) => entry.status === 'fail').length;

  const report = {
    schemaVersion: 'discovery-pack-validation-report/v1',
    contractId: 'discovery-pack-validation-report.v1',
    generatedAt: new Date().toISOString(),
    schemaPath: toRelativePath(resolvedSchema),
    sourcePatterns: options.sources,
    strictApproved: options.strictApproved,
    failOn: options.failOn,
    scannedFiles: sourceFiles.length,
    passedFiles,
    warningFiles,
    failedFiles,
    status: failedFiles > 0 ? 'fail' : failOnReasons.length > 0 ? 'fail' : warningFiles > 0 ? 'warn' : 'pass',
    summary: aggregateSummary,
    files: fileReports,
  };

  const outputs = writeReport(report, options.format, options.outputDir);
  if (outputs.jsonPath) {
    process.stdout.write(`[discovery-pack] report(json): ${toRelativePath(outputs.jsonPath)}\n`);
  }
  if (outputs.markdownPath) {
    process.stdout.write(`[discovery-pack] report(md): ${toRelativePath(outputs.markdownPath)}\n`);
  }

  if (failedFiles > 0) {
    process.stderr.write(`[discovery-pack] validation failed (${failedFiles} file(s))\n`);
    return 1;
  }
  if (failOnReasons.length > 0) {
    process.stderr.write(
      `[discovery-pack] fail-on condition matched: ${failOnReasons.join(', ')}\n`,
    );
    return 1;
  }

  process.stdout.write(
    `[discovery-pack] validation ${warningFiles > 0 ? 'completed with warnings' : 'passed'} (${sourceFiles.length} file(s))\n`,
  );
  return 0;
}

try {
  const options = parseArgs(process.argv);
  if (options.help) {
    printHelp();
    process.exit(0);
  }
  process.exit(validateDiscoveryPackSources(options));
} catch (error) {
  const exitCode = typeof error?.exitCode === 'number' ? error.exitCode : 1;
  process.stderr.write(`[discovery-pack] ${error instanceof Error ? error.message : String(error)}\n`);
  process.exit(exitCode);
}
