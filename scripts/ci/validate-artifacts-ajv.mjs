#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import { globSync } from 'glob';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const DEFAULT_REPO_ROOT = path.resolve(__dirname, '..', '..');
const DEFAULT_OUTPUT_DIR = path.join('artifacts', 'schema-validation');

export const DEFAULT_RULES = [
  {
    id: 'verify-lite-run-summary',
    schemaPath: 'schema/verify-lite-run-summary.schema.json',
    patterns: ['artifacts/verify-lite/verify-lite-run-summary.json'],
  },
  {
    id: 'adapter-summary',
    schemaPath: 'docs/schemas/artifacts-adapter-summary.schema.json',
    patterns: [
      'artifacts/adapters/**/summary.json',
      'artifacts/lighthouse/**/summary.json',
    ],
  },
  {
    id: 'report-envelope',
    schemaPath: 'schema/envelope.schema.json',
    patterns: [
      'artifacts/report-envelope.json',
      'artifacts/**/report-envelope.json',
      'artifacts/**/*-envelope.json',
    ],
  },
  {
    id: 'formal-summary-v1',
    schemaPath: 'schema/formal-summary-v1.schema.json',
    patterns: ['artifacts/formal/formal-summary-v1.json'],
  },
  {
    id: 'flow-fixture',
    schemaPath: 'schema/flow.schema.json',
    patterns: ['fixtures/flow/sample.flow.json'],
  },
  {
    id: 'properties-summary',
    schemaPath: 'docs/schemas/artifacts-properties-summary.schema.json',
    patterns: ['artifacts/properties/summary.json'],
    iterateArrayItems: true,
  },
  {
    id: 'mbt-summary',
    schemaPath: 'docs/schemas/artifacts-mbt-summary.schema.json',
    patterns: ['artifacts/mbt/summary.json'],
  },
  {
    id: 'codex-result',
    schemaPath: 'docs/schemas/artifacts-codex-result.schema.json',
    patterns: ['artifacts/codex/result-*.json'],
  },
];

const PRELOAD_SCHEMA_PATTERNS = [
  'schema/**/*.schema.json',
  'docs/schemas/*.schema.json',
];

function toPosix(value) {
  return value.replace(/\\/g, '/');
}

function parseBooleanFlag(rawValue, defaultValue = false) {
  if (rawValue === undefined || rawValue === null) {
    return defaultValue;
  }
  const normalized = String(rawValue).trim().toLowerCase();
  if (normalized.length === 0) {
    return defaultValue;
  }
  return normalized === '1'
    || normalized === 'true'
    || normalized === 'yes'
    || normalized === 'on';
}

export function parseArgs(argv = process.argv) {
  const options = {
    rootDir: DEFAULT_REPO_ROOT,
    strict: parseBooleanFlag(process.env.ARTIFACTS_VALIDATE_STRICT, false),
    outputDir: DEFAULT_OUTPUT_DIR,
    summaryJsonPath: null,
    summaryMarkdownPath: null,
    errorsJsonPath: null,
    help: false,
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
    if (arg === '--strict') {
      options.strict = true;
      continue;
    }
    if (arg === '--no-strict') {
      options.strict = false;
      continue;
    }
    if (arg.startsWith('--strict=')) {
      options.strict = parseBooleanFlag(arg.slice('--strict='.length), false);
      continue;
    }
    if (arg === '--root') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --root');
      }
      options.rootDir = path.resolve(next);
      index += 1;
      continue;
    }
    if (arg.startsWith('--root=')) {
      options.rootDir = path.resolve(arg.slice('--root='.length));
      continue;
    }
    if (arg === '--output-dir') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --output-dir');
      }
      options.outputDir = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--output-dir=')) {
      options.outputDir = arg.slice('--output-dir='.length);
      continue;
    }
    if (arg === '--summary-json') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --summary-json');
      }
      options.summaryJsonPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--summary-json=')) {
      options.summaryJsonPath = arg.slice('--summary-json='.length);
      continue;
    }
    if (arg === '--summary-md') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --summary-md');
      }
      options.summaryMarkdownPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--summary-md=')) {
      options.summaryMarkdownPath = arg.slice('--summary-md='.length);
      continue;
    }
    if (arg === '--errors-json') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --errors-json');
      }
      options.errorsJsonPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--errors-json=')) {
      options.errorsJsonPath = arg.slice('--errors-json='.length);
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(`Validate artifacts JSON files against JSON Schema contracts.

Usage:
  node scripts/ci/validate-artifacts-ajv.mjs [options]

Options:
  --strict                 Exit 1 when schema violations exist
  --no-strict              Always exit 0 (default for non-blocking runs)
  --strict=<bool>          Explicit strict flag (true/false/1/0)
  --root <path>            Repository root path
  --output-dir <path>      Output directory (default: artifacts/schema-validation)
  --summary-json <path>    Summary JSON output path
  --summary-md <path>      Summary Markdown output path
  --errors-json <path>     Detailed errors JSON output path
  --help, -h               Show this help

Environment:
  ARTIFACTS_VALIDATE_STRICT=1 to enable strict mode.
`);
}

function ensureParentDir(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function readJsonFile(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function resolveOutputPaths(rootDir, options) {
  const outputDir = path.resolve(rootDir, options.outputDir);
  return {
    outputDir,
    summaryJsonPath: path.resolve(rootDir, options.summaryJsonPath ?? path.join(options.outputDir, 'summary.json')),
    summaryMarkdownPath: path.resolve(rootDir, options.summaryMarkdownPath ?? path.join(options.outputDir, 'summary.md')),
    errorsJsonPath: path.resolve(rootDir, options.errorsJsonPath ?? path.join(options.outputDir, 'errors.json')),
  };
}

function listFilesByPatterns(patterns, rootDir) {
  const matched = new Set();
  for (const pattern of patterns) {
    const files = globSync(pattern, {
      cwd: rootDir,
      nodir: true,
      ignore: ['**/node_modules/**', '**/.git/**'],
    });
    for (const file of files) {
      matched.add(toPosix(file));
    }
  }
  return [...matched].sort((left, right) => left.localeCompare(right));
}

function preloadSchemas(ajv, rootDir) {
  const schemaFiles = listFilesByPatterns(PRELOAD_SCHEMA_PATTERNS, rootDir);
  for (const relativePath of schemaFiles) {
    const absolutePath = path.resolve(rootDir, relativePath);
    try {
      const schema = readJsonFile(absolutePath);
      if (!schema || typeof schema !== 'object' || typeof schema.$id !== 'string') {
        continue;
      }
      const schemaDraft = typeof schema.$schema === 'string' ? schema.$schema : '';
      if (schemaDraft.includes('draft-07')) {
        continue;
      }
      if (ajv.getSchema(schema.$id)) {
        continue;
      }
      ajv.addSchema(schema);
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      process.stderr.write(`[artifacts:validate] failed to preload schema ${relativePath}: ${message}\n`);
    }
  }
}

function buildAjv() {
  const ajv = new Ajv2020({ allErrors: true, strict: false, allowUnionTypes: true });
  addFormats(ajv);
  return ajv;
}

function normalizeInstancePath(prefix, instancePath) {
  const localPath = (instancePath && instancePath.length > 0) ? instancePath : '/';
  if (!prefix) {
    return localPath;
  }
  if (localPath === '/') {
    return prefix;
  }
  if (prefix.endsWith('/')) {
    return `${prefix}${localPath.slice(1)}`;
  }
  return `${prefix}${localPath}`;
}

function collectKeywordCounts(errors) {
  const counts = {};
  for (const error of errors) {
    counts[error.keyword] = (counts[error.keyword] ?? 0) + 1;
  }
  return counts;
}

function escapeMarkdownValue(value) {
  return String(value ?? '')
    .replace(/\\/g, '\\\\')
    .replace(/\|/g, '\\|')
    .replace(/`/g, '\\`')
    .replace(/\r?\n/g, ' ');
}

function renderSummaryMarkdown(summary, errors) {
  const lines = [];
  lines.push('# Artifacts Schema Validation');
  lines.push('');
  lines.push(`- strict: ${summary.strict}`);
  lines.push(`- generatedAtUtc: ${summary.generatedAtUtc}`);
  lines.push(`- durationMs: ${summary.totals.durationMs}`);
  lines.push(`- rules: ${summary.totals.rules}`);
  lines.push(`- matchedFiles: ${summary.totals.matchedFiles}`);
  lines.push(`- validatedFiles: ${summary.totals.validatedFiles}`);
  lines.push(`- passedFiles: ${summary.totals.passedFiles}`);
  lines.push(`- failedFiles: ${summary.totals.failedFiles}`);
  lines.push(`- errorCount: ${summary.totals.errorCount}`);
  lines.push(`- schemaRuleErrors: ${summary.totals.schemaRuleErrors}`);
  lines.push('');
  lines.push('## Rules');
  lines.push('');
  lines.push('| Rule | Schema | Matched | Validated | Failed | Status |');
  lines.push('| --- | --- | ---: | ---: | ---: | --- |');
  for (const rule of summary.rules) {
    let status = rule.skipped ? `skipped (${rule.skipReason ?? 'no files'})` : (rule.failedFiles > 0 ? 'failed' : 'ok');
    if (rule.ruleError) {
      status = `rule_error (${rule.ruleError})`;
    }
    lines.push(
      `| ${escapeMarkdownValue(rule.id)} | \`${escapeMarkdownValue(rule.schemaPath)}\` | ${rule.matchedFiles} | ${rule.validatedFiles} | ${rule.failedFiles} | ${escapeMarkdownValue(status)} |`
    );
  }

  const keywordEntries = Object.entries(summary.keywordCounts).sort(([left], [right]) => left.localeCompare(right));
  if (keywordEntries.length > 0) {
    lines.push('');
    lines.push('## Error Types');
    lines.push('');
    for (const [keyword, count] of keywordEntries) {
      lines.push(`- ${keyword}: ${count}`);
    }
  }

  if (errors.length > 0) {
    lines.push('');
    lines.push('## Top Errors');
    lines.push('');
    for (const error of errors.slice(0, 20)) {
      lines.push(
        `- [${escapeMarkdownValue(error.ruleId)}] \`${escapeMarkdownValue(error.file)}\` \`${escapeMarkdownValue(error.instancePath)}\` ${escapeMarkdownValue(error.message)}`
      );
    }
  }

  lines.push('');
  return `${lines.join('\n')}\n`;
}

function writeJson(filePath, payload) {
  ensureParentDir(filePath);
  fs.writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`);
}

function appendStepSummary(markdown) {
  const summaryPath = process.env.GITHUB_STEP_SUMMARY;
  if (!summaryPath) {
    return;
  }
  ensureParentDir(summaryPath);
  fs.appendFileSync(summaryPath, markdown);
}

function toDisplayPath(rootDir, targetPath) {
  const relative = path.relative(rootDir, targetPath);
  return toPosix(relative.length > 0 ? relative : '.');
}

export function validateArtifactsAjv({
  rootDir = DEFAULT_REPO_ROOT,
  strict = false,
  rules = DEFAULT_RULES,
  outputDir = DEFAULT_OUTPUT_DIR,
  summaryJsonPath = null,
  summaryMarkdownPath = null,
  errorsJsonPath = null,
} = {}) {
  const startedAt = Date.now();
  const resolvedRootDir = path.resolve(rootDir);
  const outputPaths = resolveOutputPaths(resolvedRootDir, {
    outputDir,
    summaryJsonPath,
    summaryMarkdownPath,
    errorsJsonPath,
  });
  const ajv = buildAjv();
  preloadSchemas(ajv, resolvedRootDir);

  const errors = [];
  const ruleSummaries = [];
  let matchedFiles = 0;
  let validatedFiles = 0;
  let passedFiles = 0;
  let failedFiles = 0;
  let schemaRuleErrors = 0;

  for (const rule of rules) {
    const ruleSummary = {
      id: rule.id,
      schemaPath: rule.schemaPath,
      patterns: [...rule.patterns],
      matchedFiles: 0,
      validatedFiles: 0,
      passedFiles: 0,
      failedFiles: 0,
      skipped: false,
      skipReason: null,
      ruleError: null,
    };

    const schemaAbsolutePath = path.resolve(resolvedRootDir, rule.schemaPath);
    if (!fs.existsSync(schemaAbsolutePath)) {
      const errorRecord = {
        ruleId: rule.id,
        file: toPosix(rule.schemaPath),
        schemaPath: toPosix(rule.schemaPath),
        keyword: 'schema_missing',
        instancePath: '/',
        message: 'schema file is missing',
      };
      errors.push(errorRecord);
      ruleSummary.ruleError = 'schema_missing';
      schemaRuleErrors += 1;
      ruleSummaries.push(ruleSummary);
      continue;
    }

    let schema;
    let validate;
    try {
      schema = readJsonFile(schemaAbsolutePath);
      if (schema && typeof schema === 'object' && typeof schema.$id === 'string' && ajv.getSchema(schema.$id)) {
        validate = ajv.getSchema(schema.$id);
      } else {
        validate = ajv.compile(schema);
      }
      if (typeof validate !== 'function') {
        throw new Error('compiled validator is unavailable');
      }
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      const errorRecord = {
        ruleId: rule.id,
        file: toPosix(rule.schemaPath),
        schemaPath: toPosix(rule.schemaPath),
        keyword: 'schema_compile_error',
        instancePath: '/',
        message,
      };
      errors.push(errorRecord);
      ruleSummary.ruleError = 'schema_compile_error';
      schemaRuleErrors += 1;
      ruleSummaries.push(ruleSummary);
      continue;
    }

    const files = listFilesByPatterns(rule.patterns, resolvedRootDir);
    ruleSummary.matchedFiles = files.length;
    matchedFiles += files.length;

    if (files.length === 0) {
      ruleSummary.skipped = true;
      ruleSummary.skipReason = 'no files matched';
      ruleSummaries.push(ruleSummary);
      continue;
    }

    for (const file of files) {
      const absolutePath = path.resolve(resolvedRootDir, file);
      let payload;
      try {
        payload = readJsonFile(absolutePath);
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        errors.push({
          ruleId: rule.id,
          file,
          schemaPath: toPosix(rule.schemaPath),
          keyword: 'invalid_json',
          instancePath: '/',
          message: `failed to parse JSON: ${message}`,
        });
        ruleSummary.failedFiles += 1;
        failedFiles += 1;
        ruleSummary.validatedFiles += 1;
        validatedFiles += 1;
        continue;
      }

      const payloadEntries = (rule.iterateArrayItems && Array.isArray(payload))
        ? payload.map((item, index) => ({ item, pathPrefix: `/${index}` }))
        : [{ item: payload, pathPrefix: '' }];

      let fileHasFailure = false;
      for (const entry of payloadEntries) {
        const isValid = validate(entry.item);
        if (isValid) {
          continue;
        }
        fileHasFailure = true;
        for (const error of validate.errors ?? []) {
          errors.push({
            ruleId: rule.id,
            file,
            schemaPath: toPosix(rule.schemaPath),
            keyword: error.keyword ?? 'validation_error',
            instancePath: normalizeInstancePath(entry.pathPrefix, error.instancePath),
            message: error.message ?? 'schema validation failed',
          });
        }
      }

      ruleSummary.validatedFiles += 1;
      validatedFiles += 1;
      if (fileHasFailure) {
        ruleSummary.failedFiles += 1;
        failedFiles += 1;
      } else {
        ruleSummary.passedFiles += 1;
        passedFiles += 1;
      }
    }

    ruleSummaries.push(ruleSummary);
  }

  const summary = {
    schemaVersion: '1.0.0',
    generatedAtUtc: new Date().toISOString(),
    strict,
    rootDir: toDisplayPath(resolvedRootDir, resolvedRootDir),
    totals: {
      rules: ruleSummaries.length,
      matchedFiles,
      validatedFiles,
      passedFiles,
      failedFiles,
      errorCount: errors.length,
      schemaRuleErrors,
      durationMs: Date.now() - startedAt,
    },
    keywordCounts: collectKeywordCounts(errors),
    rules: ruleSummaries,
    output: {
      summaryJsonPath: toDisplayPath(resolvedRootDir, outputPaths.summaryJsonPath),
      summaryMarkdownPath: toDisplayPath(resolvedRootDir, outputPaths.summaryMarkdownPath),
      errorsJsonPath: toDisplayPath(resolvedRootDir, outputPaths.errorsJsonPath),
    },
    topErrors: errors.slice(0, 20),
  };

  const markdown = renderSummaryMarkdown(summary, errors);
  writeJson(outputPaths.summaryJsonPath, summary);
  writeJson(outputPaths.errorsJsonPath, {
    schemaVersion: '1.0.0',
    generatedAtUtc: summary.generatedAtUtc,
    strict,
    errors,
  });
  ensureParentDir(outputPaths.summaryMarkdownPath);
  fs.writeFileSync(outputPaths.summaryMarkdownPath, markdown);
  appendStepSummary(markdown);

  const exitCode = strict && errors.length > 0 ? 1 : 0;
  return {
    exitCode,
    summary,
    errors,
    outputPaths,
  };
}

export function isExecutedAsMain(metaUrl, argvPath = process.argv[1]) {
  if (!argvPath || typeof argvPath !== 'string') {
    return false;
  }
  try {
    const modulePath = path.resolve(fileURLToPath(metaUrl));
    const entryPath = path.resolve(argvPath);
    return modulePath === entryPath;
  } catch {
    return false;
  }
}

export function main(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return { exitCode: 0 };
  }
  const result = validateArtifactsAjv(options);
  process.stdout.write(
    `[artifacts:validate] strict=${result.summary.strict} `
      + `validated=${result.summary.totals.validatedFiles} `
      + `failed=${result.summary.totals.failedFiles} `
      + `errors=${result.summary.totals.errorCount}\n`
  );
  process.stdout.write(`[artifacts:validate] summary: ${result.summary.output.summaryJsonPath}\n`);
  process.stdout.write(`[artifacts:validate] errors: ${result.summary.output.errorsJsonPath}\n`);
  return result;
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  try {
    const result = main(process.argv);
    process.exit(result.exitCode);
  } catch (error) {
    const message = error instanceof Error ? error.stack ?? error.message : String(error);
    process.stderr.write(`[artifacts:validate] fatal: ${message}\n`);
    process.exit(2);
  }
}
