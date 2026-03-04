#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const reportPath = process.argv[2] ?? 'artifacts/ci/automation-report.json';
const schemaPath = process.argv[3] ?? 'schema/automation-observability-v1.schema.json';

const resolvedReport = path.resolve(reportPath);
const resolvedSchema = path.resolve(schemaPath);

if (!fs.existsSync(resolvedReport)) {
  console.warn(`[automation-report] report not found at ${resolvedReport}; skipping validation`);
  process.exit(0);
}

if (!fs.existsSync(resolvedSchema)) {
  console.error(`[automation-report] schema not found at ${resolvedSchema}`);
  process.exit(1);
}

let report;
let schema;
try {
  report = JSON.parse(fs.readFileSync(resolvedReport, 'utf8'));
} catch (error) {
  console.error(`[automation-report] failed to parse ${resolvedReport}:`, error);
  process.exit(1);
}

try {
  schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
} catch (error) {
  console.error(`[automation-report] failed to parse schema ${resolvedSchema}:`, error);
  process.exit(1);
}

const ajv = new Ajv2020({ allErrors: true, strict: true });
addFormats(ajv);
const validate = ajv.compile(schema);

if (!validate(report)) {
  console.error('[automation-report] schema validation failed');
  for (const err of validate.errors ?? []) {
    console.error(`  • ${err.instancePath || '/'} ${err.message}`);
  }
  process.exit(1);
}

console.log(`[automation-report] report validated against ${resolvedSchema}`);
