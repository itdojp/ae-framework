#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const manifestPath = process.argv[2] ?? 'artifacts/run-manifest.json';
const schemaPath = process.argv[3] ?? 'schema/run-manifest.schema.json';

const resolvedManifest = path.resolve(manifestPath);
const resolvedSchema = path.resolve(schemaPath);

if (!fs.existsSync(resolvedManifest)) {
  console.warn(`[run-manifest] manifest not found at ${resolvedManifest}; skipping schema validation`);
  process.exit(0);
}

if (!fs.existsSync(resolvedSchema)) {
  console.error(`[run-manifest] schema not found at ${resolvedSchema}`);
  process.exit(1);
}

let data;
let schema;
try {
  data = JSON.parse(fs.readFileSync(resolvedManifest, 'utf8'));
} catch (error) {
  console.error(`[run-manifest] failed to read manifest ${resolvedManifest}:`, error);
  process.exit(1);
}

try {
  schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
} catch (error) {
  console.error(`[run-manifest] failed to read schema ${resolvedSchema}:`, error);
  process.exit(1);
}

const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);
const metadataSchemaPath = path.resolve(path.dirname(resolvedSchema), 'artifact-metadata.schema.json');
if (fs.existsSync(metadataSchemaPath)) {
  try {
    const metadataSchema = JSON.parse(fs.readFileSync(metadataSchemaPath, 'utf8'));
    ajv.addSchema(metadataSchema);
  } catch (error) {
    console.error(`[run-manifest] failed to read metadata schema ${metadataSchemaPath}:`, error);
    process.exit(1);
  }
} else if (JSON.stringify(schema).includes('artifact-metadata.schema.json')) {
  console.error(`[run-manifest] metadata schema not found at ${metadataSchemaPath}`);
  process.exit(1);
}

const validate = ajv.compile(schema);
const valid = validate(data);
if (!valid) {
  console.error('[run-manifest] manifest schema validation failed');
  for (const err of validate.errors ?? []) {
    console.error(`  • ${err.instancePath || '/'} ${err.message}`);
  }
  process.exit(1);
}

console.log(`[run-manifest] manifest validated against ${resolvedSchema}`);

