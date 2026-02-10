#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

function parseArgs(argv) {
  const args = {
    require: false,
    file: null,
    schema: null,
  };
  for (let i = 2; i < argv.length; i += 1) {
    const a = argv[i];
    if (a === '--require') {
      args.require = true;
    } else if (!args.file) {
      args.file = a;
    } else if (!args.schema) {
      args.schema = a;
    }
  }
  return args;
}

const parsed = parseArgs(process.argv);
const summaryPath = parsed.file ?? 'artifacts/formal/formal-summary-v1.json';
const schemaPath = parsed.schema ?? 'schema/formal-summary-v1.schema.json';

const resolvedSummary = path.resolve(summaryPath);
const resolvedSchema = path.resolve(schemaPath);

if (!fs.existsSync(resolvedSchema)) {
  console.error(`[formal-summary/v1] schema not found at ${resolvedSchema}`);
  process.exit(1);
}

if (!fs.existsSync(resolvedSummary)) {
  const msg = `[formal-summary/v1] summary not found at ${resolvedSummary}`;
  if (parsed.require) {
    console.error(msg);
    process.exit(1);
  }
  console.warn(`${msg}; skipping schema validation`);
  process.exit(0);
}

let data;
let schema;
try {
  data = JSON.parse(fs.readFileSync(resolvedSummary, 'utf8'));
} catch (error) {
  console.error(`[formal-summary/v1] failed to read summary ${resolvedSummary}:`, error);
  process.exit(1);
}

try {
  schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
} catch (error) {
  console.error(`[formal-summary/v1] failed to read schema ${resolvedSchema}:`, error);
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
    console.error(`[formal-summary/v1] failed to read metadata schema ${metadataSchemaPath}:`, error);
    process.exit(1);
  }
} else if (JSON.stringify(schema).includes('artifact-metadata.schema.json')) {
  console.error(`[formal-summary/v1] metadata schema not found at ${metadataSchemaPath}`);
  process.exit(1);
}

const validate = ajv.compile(schema);
const valid = validate(data);
if (!valid) {
  console.error('[formal-summary/v1] schema validation failed');
  for (const err of validate.errors ?? []) {
    console.error(`  • ${err.instancePath || '/'} ${err.message}`);
  }
  process.exit(1);
}

console.log(`[formal-summary/v1] summary validated against ${resolvedSchema}`);

