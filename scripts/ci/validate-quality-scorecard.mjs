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
const summaryPath = parsed.file ?? 'artifacts/quality/quality-scorecard.json';
const schemaPath = parsed.schema ?? 'schema/quality-scorecard.schema.json';

const resolvedSummary = path.resolve(summaryPath);
const resolvedSchema = path.resolve(schemaPath);

if (!fs.existsSync(resolvedSchema)) {
  console.error(`[quality-scorecard] schema not found at ${resolvedSchema}`);
  process.exit(1);
}

if (!fs.existsSync(resolvedSummary)) {
  const message = `[quality-scorecard] summary not found at ${resolvedSummary}`;
  if (parsed.require) {
    console.error(message);
    process.exit(1);
  }
  console.warn(`${message}; skipping schema validation`);
  process.exit(0);
}

const schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
const payload = JSON.parse(fs.readFileSync(resolvedSummary, 'utf8'));

const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);
const metadataSchemaPath = path.resolve(path.dirname(resolvedSchema), 'artifact-metadata.schema.json');
if (fs.existsSync(metadataSchemaPath)) {
  ajv.addSchema(JSON.parse(fs.readFileSync(metadataSchemaPath, 'utf8')));
}

const validate = ajv.compile(schema);
if (!validate(payload)) {
  console.error('[quality-scorecard] schema validation failed');
  for (const error of validate.errors ?? []) {
    console.error(`  • ${error.instancePath || '/'} ${error.message}`);
  }
  process.exit(1);
}

console.log(`[quality-scorecard] summary validated against ${resolvedSchema}`);
