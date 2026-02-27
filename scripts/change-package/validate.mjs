#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_INPUT_PATH = 'artifacts/change-package/change-package.json';
const DEFAULT_SCHEMA_PATH = 'schema/change-package.schema.json';
const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/change-package/change-package-validation.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/change-package/change-package-validation.md';

function splitCommaValues(raw) {
  if (!raw) return [];
  return raw
    .split(',')
    .map((entry) => String(entry || '').trim())
    .filter(Boolean);
}

function toUnique(values) {
  return [...new Set(values)];
}

function parseArgs(argv = process.argv) {
  const options = {
    inputPath: DEFAULT_INPUT_PATH,
    schemaPath: DEFAULT_SCHEMA_PATH,
    outputJsonPath: DEFAULT_OUTPUT_JSON_PATH,
    outputMarkdownPath: DEFAULT_OUTPUT_MD_PATH,
    strict: false,
    requiredEvidenceIds: [],
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    const readValue = (name) => {
      if (!next || next.startsWith('-')) {
        throw new Error(`missing value for ${name}`);
      }
      index += 1;
      return next;
    };

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--file' || arg === '--input') {
      options.inputPath = readValue(arg);
      continue;
    }
    if (arg.startsWith('--file=')) {
      options.inputPath = arg.slice('--file='.length);
      continue;
    }
    if (arg.startsWith('--input=')) {
      options.inputPath = arg.slice('--input='.length);
      continue;
    }
    if (arg === '--schema') {
      options.schemaPath = readValue('--schema');
      continue;
    }
    if (arg.startsWith('--schema=')) {
      options.schemaPath = arg.slice('--schema='.length);
      continue;
    }
    if (arg === '--output-json') {
      options.outputJsonPath = readValue('--output-json');
      continue;
    }
    if (arg.startsWith('--output-json=')) {
      options.outputJsonPath = arg.slice('--output-json='.length);
      continue;
    }
    if (arg === '--output-md') {
      options.outputMarkdownPath = readValue('--output-md');
      continue;
    }
    if (arg.startsWith('--output-md=')) {
      options.outputMarkdownPath = arg.slice('--output-md='.length);
      continue;
    }
    if (arg === '--required-evidence') {
      options.requiredEvidenceIds.push(...splitCommaValues(readValue('--required-evidence')));
      continue;
    }
    if (arg.startsWith('--required-evidence=')) {
      options.requiredEvidenceIds.push(...splitCommaValues(arg.slice('--required-evidence='.length)));
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
    throw new Error(`unknown option: ${arg}`);
  }

  const envRequiredEvidence = splitCommaValues(process.env.AE_CHANGE_PACKAGE_REQUIRED_EVIDENCE || '');
  if (options.requiredEvidenceIds.length === 0 && envRequiredEvidence.length > 0) {
    options.requiredEvidenceIds = envRequiredEvidence;
  }

  options.requiredEvidenceIds = toUnique(options.requiredEvidenceIds);
  return options;
}

function printHelp() {
  process.stdout.write(
    `Change Package validator\n\n`
    + `Usage:\n`
    + `  node scripts/change-package/validate.mjs [options]\n\n`
    + `Options:\n`
    + `  --file <path>                 input Change Package JSON (default: ${DEFAULT_INPUT_PATH})\n`
    + `  --schema <path>               JSON Schema path (default: ${DEFAULT_SCHEMA_PATH})\n`
    + `  --output-json <path>          output JSON report (default: ${DEFAULT_OUTPUT_JSON_PATH})\n`
    + `  --output-md <path>            output Markdown report (default: ${DEFAULT_OUTPUT_MD_PATH})\n`
    + `  --required-evidence <ids>     comma-separated evidence IDs to require\n`
    + `  --strict                      fail on missing required evidence\n`
    + `  --help, -h                    show help\n`,
  );
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function readJsonFile(filePath) {
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) {
    throw new Error(`file not found: ${resolved}`);
  }
  return JSON.parse(fs.readFileSync(resolved, 'utf8'));
}

function validateSchema(schema, payload) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const ok = validate(payload);
  return {
    ok,
    errors: validate.errors || [],
  };
}

function resolveRequiredEvidenceIds(options, payload) {
  if (options.requiredEvidenceIds.length > 0) {
    return options.requiredEvidenceIds;
  }
  const highRisk = Boolean(payload?.risk?.isHighRisk);
  return highRisk
    ? ['verifyLiteSummary', 'policyGateSummary', 'harnessHealth']
    : ['verifyLiteSummary'];
}

function evaluateEvidence(payload, requiredEvidenceIds) {
  const items = Array.isArray(payload?.evidence?.items) ? payload.evidence.items : [];
  const itemMap = new Map();
  for (const item of items) {
    const id = String(item?.id || '').trim();
    if (!id) continue;
    itemMap.set(id, item);
  }

  const missingRequiredEvidence = requiredEvidenceIds
    .map((id) => {
      const item = itemMap.get(id);
      const present = Boolean(item?.present);
      if (present) return null;
      return {
        id,
        present: false,
        reason: item ? 'present=false' : 'missing-item',
      };
    })
    .filter(Boolean);

  const presentCountActual = items.filter((item) => item?.present === true).length;
  const missingCountActual = items.length - presentCountActual;
  const presentCountDeclared = Number(payload?.evidence?.presentCount);
  const missingCountDeclared = Number(payload?.evidence?.missingCount);

  const countMismatches = [];
  if (Number.isFinite(presentCountDeclared) && presentCountDeclared !== presentCountActual) {
    countMismatches.push(
      `presentCount mismatch: declared=${presentCountDeclared}, actual=${presentCountActual}`,
    );
  }
  if (Number.isFinite(missingCountDeclared) && missingCountDeclared !== missingCountActual) {
    countMismatches.push(
      `missingCount mismatch: declared=${missingCountDeclared}, actual=${missingCountActual}`,
    );
  }

  return {
    requiredEvidenceIds,
    missingRequiredEvidence,
    countMismatches,
    presentCountActual,
    missingCountActual,
    itemCount: items.length,
  };
}

function normalizeAjvErrors(errors) {
  return (errors || []).map((error) => {
    const instancePath = error.instancePath || '/';
    const keyword = error.keyword || 'unknown';
    const message = error.message || 'schema validation error';
    return `${instancePath} [${keyword}] ${message}`;
  });
}

function buildValidationReport(options, schemaResult, evidenceResult) {
  const errors = [];
  const warnings = [];

  if (!schemaResult.ok) {
    errors.push(...normalizeAjvErrors(schemaResult.errors));
  }

  if (evidenceResult.missingRequiredEvidence.length > 0) {
    const message = `missing required evidence: ${evidenceResult.missingRequiredEvidence.map((item) => item.id).join(', ')}`;
    if (options.strict) {
      errors.push(message);
    } else {
      warnings.push(message);
    }
  }

  if (evidenceResult.countMismatches.length > 0) {
    warnings.push(...evidenceResult.countMismatches);
  }

  const result = errors.length > 0 ? 'fail' : (warnings.length > 0 ? 'warn' : 'pass');
  return {
    schemaVersion: 'change-package-validation/v1',
    generatedAt: new Date().toISOString(),
    strict: options.strict,
    result,
    schema: {
      path: options.schemaPath,
      ok: schemaResult.ok,
      errors: normalizeAjvErrors(schemaResult.errors),
    },
    evidence: {
      requiredEvidenceIds: evidenceResult.requiredEvidenceIds,
      missingRequiredEvidence: evidenceResult.missingRequiredEvidence,
      itemCount: evidenceResult.itemCount,
      presentCountActual: evidenceResult.presentCountActual,
      missingCountActual: evidenceResult.missingCountActual,
    },
    errors,
    warnings,
  };
}

function renderMarkdown(report) {
  const lines = [
    '### Change Package Validation',
    `- result: ${report.result.toUpperCase()}`,
    `- strict: ${report.strict}`,
    `- schema: ${report.schema.ok ? 'PASS' : 'FAIL'}`,
    `- required evidence: ${report.evidence.requiredEvidenceIds.length > 0 ? report.evidence.requiredEvidenceIds.join(', ') : '(none)'}`,
    `- missing required evidence: ${report.evidence.missingRequiredEvidence.length > 0 ? report.evidence.missingRequiredEvidence.map((item) => item.id).join(', ') : '(none)'}`,
    `- evidence present/missing(actual): ${report.evidence.presentCountActual}/${report.evidence.missingCountActual}`,
  ];

  if (report.errors.length > 0) {
    lines.push('- errors:');
    for (const error of report.errors) {
      lines.push(`  - ${error}`);
    }
  }
  if (report.warnings.length > 0) {
    lines.push('- warnings:');
    for (const warning of report.warnings) {
      lines.push(`  - ${warning}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

function persistReport(report, markdown, options) {
  ensureDirectory(options.outputJsonPath);
  fs.writeFileSync(options.outputJsonPath, `${JSON.stringify(report, null, 2)}\n`);

  ensureDirectory(options.outputMarkdownPath);
  fs.writeFileSync(options.outputMarkdownPath, `${markdown.trimEnd()}\n`);
}

async function run(options = parseArgs(process.argv)) {
  if (options.help) {
    printHelp();
    return null;
  }

  const payload = readJsonFile(options.inputPath);
  const schema = readJsonFile(options.schemaPath);
  const schemaResult = validateSchema(schema, payload);
  const requiredEvidenceIds = resolveRequiredEvidenceIds(options, payload);
  const evidenceResult = evaluateEvidence(payload, requiredEvidenceIds);
  const report = buildValidationReport(options, schemaResult, evidenceResult);
  const markdown = renderMarkdown(report);
  persistReport(report, markdown, options);

  process.stdout.write(markdown);
  if (report.result === 'fail') {
    process.exitCode = 1;
  }
  return report;
}

function isDirectExecution() {
  const entry = process.argv[1];
  if (!entry) return false;
  return import.meta.url === pathToFileURL(resolve(entry)).href;
}

if (isDirectExecution()) {
  try {
    await run();
  } catch (error) {
    const message = error instanceof Error ? error.stack || error.message : String(error);
    process.stderr.write(`[change-package:validate] ${message}\n`);
    process.exit(1);
  }
}

export {
  buildValidationReport,
  parseArgs,
  renderMarkdown,
  run,
};
