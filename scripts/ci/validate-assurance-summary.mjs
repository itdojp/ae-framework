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
  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--require') {
      args.require = true;
    } else if (!args.file) {
      args.file = arg;
    } else if (!args.schema) {
      args.schema = arg;
    }
  }
  return args;
}

const parsed = parseArgs(process.argv);
const summaryPath = parsed.file ?? 'artifacts/assurance/assurance-summary.json';
const schemaPath = parsed.schema ?? 'schema/assurance-summary.schema.json';

const resolvedSummary = path.resolve(summaryPath);
const resolvedSchema = path.resolve(schemaPath);

if (!fs.existsSync(resolvedSchema)) {
  console.error(`[assurance-summary] schema not found at ${resolvedSchema}`);
  process.exit(1);
}

if (!fs.existsSync(resolvedSummary)) {
  const message = `[assurance-summary] summary not found at ${resolvedSummary}`;
  if (parsed.require) {
    console.error(message);
    process.exit(1);
  }
  console.warn(`${message}; skipping schema validation`);
  process.exit(0);
}

let summary;
let schema;
try {
  summary = JSON.parse(fs.readFileSync(resolvedSummary, 'utf8'));
} catch (error) {
  console.error(`[assurance-summary] failed to read summary ${resolvedSummary}:`, error);
  process.exit(1);
}

try {
  schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
} catch (error) {
  console.error(`[assurance-summary] failed to read schema ${resolvedSchema}:`, error);
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
    console.error(`[assurance-summary] failed to read metadata schema ${metadataSchemaPath}:`, error);
    process.exit(1);
  }
} else if (JSON.stringify(schema).includes('artifact-metadata.schema.json')) {
  console.error(`[assurance-summary] metadata schema not found at ${metadataSchemaPath}`);
  process.exit(1);
}

const validate = ajv.compile(schema);
const valid = validate(summary);
if (!valid) {
  console.error('[assurance-summary] schema validation failed');
  for (const error of validate.errors ?? []) {
    console.error(`  • ${error.instancePath || '/'} ${error.message}`);
  }
  process.exit(1);
}

console.log(`[assurance-summary] summary validated against ${resolvedSchema}`);
