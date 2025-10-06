#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const envelopePath = process.argv[2] ?? 'artifacts/report-envelope.json';
const schemaPath = process.argv[3] ?? 'schema/report-envelope.schema.json';

const resolvedEnvelope = path.resolve(envelopePath);
const resolvedSchema = path.resolve(schemaPath);

if (!fs.existsSync(resolvedEnvelope)) {
  console.warn(`[report-envelope] envelope not found at ${resolvedEnvelope}; skipping validation`);
  process.exit(0);
}

if (!fs.existsSync(resolvedSchema)) {
  console.error(`[report-envelope] schema not found at ${resolvedSchema}`);
  process.exit(1);
}

let envelope;
let schema;
try {
  envelope = JSON.parse(fs.readFileSync(resolvedEnvelope, 'utf8'));
} catch (error) {
  console.error(`[report-envelope] failed to parse ${resolvedEnvelope}:`, error);
  process.exit(1);
}

try {
  schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
} catch (error) {
  console.error(`[report-envelope] failed to parse schema ${resolvedSchema}:`, error);
  process.exit(1);
}

const ajv = new Ajv2020({ allErrors: true, strict: true });
addFormats(ajv);
const validate = ajv.compile(schema);

if (!validate(envelope)) {
  console.error('[report-envelope] envelope schema validation failed');
  for (const err of validate.errors ?? []) {
    console.error(`  • ${err.instancePath || '/'} ${err.message}`);
  }
  process.exit(1);
}

console.log(`[report-envelope] envelope validated against ${resolvedSchema}`);
