#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const summaryPath = process.argv[2] ?? 'verify-lite-run-summary.json';
const schemaPath = process.argv[3] ?? 'schema/verify-lite-run-summary.schema.json';

const resolvedSummary = path.resolve(summaryPath);
const resolvedSchema = path.resolve(schemaPath);

if (!fs.existsSync(resolvedSummary)) {
  console.warn(`[verify-lite] summary not found at ${resolvedSummary}; skipping schema validation`);
  process.exit(0);
}

if (!fs.existsSync(resolvedSchema)) {
  console.error(`[verify-lite] schema not found at ${resolvedSchema}`);
  process.exit(1);
}

let data;
let schema;
try {
  data = JSON.parse(fs.readFileSync(resolvedSummary, 'utf8'));
} catch (error) {
  console.error(`[verify-lite] failed to read summary ${resolvedSummary}:`, error);
  process.exit(1);
}

try {
  schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
} catch (error) {
  console.error(`[verify-lite] failed to read schema ${resolvedSchema}:`, error);
  process.exit(1);
}

const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);
const validate = ajv.compile(schema);

const valid = validate(data);
if (!valid) {
  console.error('[verify-lite] summary schema validation failed');
  for (const err of validate.errors ?? []) {
    console.error(`  • ${err.instancePath || '/'} ${err.message}`);
  }
  process.exit(1);
}

console.log(`[verify-lite] summary validated against ${resolvedSchema}`);
