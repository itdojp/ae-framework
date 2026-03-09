#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { DEFAULT_POLICY_PATH, getRiskLabels, loadRiskPolicy } from '../ci/lib/risk-policy.mjs';

const __filename = fileURLToPath(import.meta.url);
const DEFAULT_INPUT_PATH = 'artifacts/plan/plan-artifact.json';
const DEFAULT_SCHEMA_PATH = 'schema/plan-artifact.schema.json';
const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/plan/plan-artifact-validation.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/plan/plan-artifact-validation.md';

function parseArgs(argv = process.argv) {
  const options = {
    inputPath: DEFAULT_INPUT_PATH,
    schemaPath: DEFAULT_SCHEMA_PATH,
    outputJsonPath: DEFAULT_OUTPUT_JSON_PATH,
    outputMarkdownPath: DEFAULT_OUTPUT_MD_PATH,
    policyPath: DEFAULT_POLICY_PATH,
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
    if (arg === '--policy') {
      options.policyPath = readValue('--policy');
      continue;
    }
    if (arg.startsWith('--policy=')) {
      options.policyPath = arg.slice('--policy='.length);
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
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(
    'Plan Artifact validator\n\n'
      + 'Usage:\n'
      + '  node scripts/plan-artifact/validate.mjs [options]\n\n'
      + 'Options:\n'
      + `  --file <path>                 input JSON (default: ${DEFAULT_INPUT_PATH})\n`
      + `  --schema <path>               schema path (default: ${DEFAULT_SCHEMA_PATH})\n`
      + `  --policy <path>               risk policy path (default: ${DEFAULT_POLICY_PATH})\n`
      + `  --output-json <path>          output JSON report (default: ${DEFAULT_OUTPUT_JSON_PATH})\n`
      + `  --output-md <path>            output Markdown report (default: ${DEFAULT_OUTPUT_MD_PATH})\n`
      + '  --help, -h                    show help\n',
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

function normalizeAjvErrors(errors) {
  return (errors || []).map((error) => {
    const instancePath = error.instancePath || '/';
    const keyword = error.keyword || 'unknown';
    const message = error.message || 'schema validation error';
    return `${instancePath} [${keyword}] ${message}`;
  });
}

function runSchemaValidation(schema, payload) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const ok = validate(payload);
  return {
    ok,
    errors: normalizeAjvErrors(validate.errors || []),
  };
}

function semanticValidation(payload, policy) {
  const errors = [];
  const warnings = [];
  const riskLabels = getRiskLabels(policy);
  const selectedRisk = String(payload?.risk?.selected || '').trim();
  if (selectedRisk !== riskLabels.low && selectedRisk !== riskLabels.high) {
    errors.push(`risk.selected must be ${riskLabels.low} or ${riskLabels.high}`);
  }
  if (
    selectedRisk === riskLabels.high
    && (!Array.isArray(payload.requiredHumanInput) || payload.requiredHumanInput.length === 0)
  ) {
    warnings.push('high-risk plan artifact has no requiredHumanInput entries');
  }
  if (Array.isArray(payload?.verificationPlan)) {
    for (const step of payload.verificationPlan) {
      if (!Array.isArray(step?.expectedEvidence) || step.expectedEvidence.length === 0) {
        warnings.push(`verification step ${step?.id || '(unknown)'} has no expectedEvidence`);
      }
    }
  }
  return { errors, warnings };
}

export function validatePlanArtifactFile(options) {
  const payload = readJsonFile(options.inputPath);
  const schema = readJsonFile(options.schemaPath);
  const policy = loadRiskPolicy(options.policyPath);
  const schemaResult = runSchemaValidation(schema, payload);
  const semanticResult = schemaResult.ok ? semanticValidation(payload, policy) : { errors: [], warnings: [] };
  const errors = [...schemaResult.errors, ...semanticResult.errors];
  const warnings = errors.length === 0 ? semanticResult.warnings : [];
  const result = errors.length > 0 ? 'fail' : (warnings.length > 0 ? 'warn' : 'pass');
  const report = {
    schemaVersion: 'plan-artifact-validation/v1',
    generatedAt: new Date().toISOString(),
    result,
    inputPath: path.resolve(options.inputPath),
    schemaPath: path.resolve(options.schemaPath),
    policyPath: path.resolve(options.policyPath),
    errors,
    warnings,
  };
  return { report, payload };
}

function renderMarkdown(report) {
  const lines = [
    '## Plan Artifact Validation',
    '',
    `- result: ${report.result.toUpperCase()}`,
    `- input: \`${report.inputPath}\``,
    `- schema: \`${report.schemaPath}\``,
    `- policy: \`${report.policyPath}\``,
    '',
  ];
  if (report.errors.length > 0) {
    lines.push('### Errors', '', ...report.errors.map((item) => `- ${item}`), '');
  }
  if (report.warnings.length > 0) {
    lines.push('### Warnings', '', ...report.warnings.map((item) => `- ${item}`), '');
  }
  if (report.errors.length === 0 && report.warnings.length === 0) {
    lines.push('- no issues', '');
  }
  return `${lines.join('\n')}\n`;
}

export { parseArgs, renderMarkdown };

export function main(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }
  const { report } = validatePlanArtifactFile(options);
  const markdown = renderMarkdown(report);
  ensureDirectory(options.outputJsonPath);
  fs.writeFileSync(path.resolve(options.outputJsonPath), `${JSON.stringify(report, null, 2)}\n`);
  ensureDirectory(options.outputMarkdownPath);
  fs.writeFileSync(path.resolve(options.outputMarkdownPath), markdown);
  process.stdout.write(`Validated ${options.inputPath}: ${report.result}\n`);
  return report.result === 'fail' ? 1 : 0;
}

if (process.argv[1] && path.resolve(process.argv[1]) === __filename) {
  try {
    process.exit(main(process.argv));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`[plan-artifact:validate] ${message}\n`);
    process.exit(1);
  }
}
