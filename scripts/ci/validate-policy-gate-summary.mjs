#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const summaryPath = process.argv[2] ?? 'artifacts/ci/policy-gate-summary.json';
const schemaPath = process.argv[3] ?? 'schema/policy-gate-summary-v1.schema.json';

const resolvedSummary = path.resolve(summaryPath);
const resolvedSchema = path.resolve(schemaPath);

if (!fs.existsSync(resolvedSummary)) {
  console.warn(`[policy-gate-summary] summary not found at ${resolvedSummary}; skipping validation`);
  process.exit(0);
}

if (!fs.existsSync(resolvedSchema)) {
  console.error(`[policy-gate-summary] schema not found at ${resolvedSchema}`);
  process.exit(1);
}

let summary;
let schema;

try {
  summary = JSON.parse(fs.readFileSync(resolvedSummary, 'utf8'));
} catch (error) {
  console.error(`[policy-gate-summary] failed to parse ${resolvedSummary}:`, error);
  process.exit(1);
}

try {
  schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
} catch (error) {
  console.error(`[policy-gate-summary] failed to parse schema ${resolvedSchema}:`, error);
  process.exit(1);
}

const ajv = new Ajv2020({ allErrors: true, strict: true });
addFormats(ajv);
const validate = ajv.compile(schema);

if (!validate(summary)) {
  console.error('[policy-gate-summary] schema validation failed');
  for (const err of validate.errors ?? []) {
    console.error(`  • ${err.instancePath || '/'} ${err.message}`);
  }
  process.exit(1);
}

console.log(`[policy-gate-summary] summary validated against ${resolvedSchema}`);
