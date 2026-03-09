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
const handoffPath = parsed.file ?? 'artifacts/handoff/ae-handoff.json';
const schemaPath = parsed.schema ?? 'schema/ae-handoff.schema.json';

const resolvedHandoff = path.resolve(handoffPath);
const resolvedSchema = path.resolve(schemaPath);

if (!fs.existsSync(resolvedSchema)) {
  console.error(`[ae-handoff] schema not found at ${resolvedSchema}`);
  process.exit(1);
}

if (!fs.existsSync(resolvedHandoff)) {
  const message = `[ae-handoff] handoff not found at ${resolvedHandoff}`;
  if (parsed.require) {
    console.error(message);
    process.exit(1);
  }
  console.warn(`${message}; skipping schema validation`);
  process.exit(0);
}

let handoff;
let schema;
try {
  handoff = JSON.parse(fs.readFileSync(resolvedHandoff, 'utf8'));
} catch (error) {
  console.error(`[ae-handoff] failed to read handoff ${resolvedHandoff}:`, error);
  process.exit(1);
}

try {
  schema = JSON.parse(fs.readFileSync(resolvedSchema, 'utf8'));
} catch (error) {
  console.error(`[ae-handoff] failed to read schema ${resolvedSchema}:`, error);
  process.exit(1);
}

const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);
const validate = ajv.compile(schema);
const valid = validate(handoff);
if (!valid) {
  console.error('[ae-handoff] schema validation failed');
  for (const error of validate.errors ?? []) {
    console.error(`  • ${error.instancePath || '/'} ${error.message}`);
  }
  process.exit(1);
}

console.log(`[ae-handoff] handoff validated against ${resolvedSchema}`);
