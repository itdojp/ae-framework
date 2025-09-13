#!/usr/bin/env node
// Validate observability traces against observability/trace-schema.yaml
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import yaml from 'yaml';
import Ajv from 'ajv';
import addFormats from 'ajv-formats';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..', '..');

function readYaml(p){ return yaml.parse(fs.readFileSync(p, 'utf8')); }
function readJson(p){ return JSON.parse(fs.readFileSync(p, 'utf8')); }

const schemaPath = path.join(repoRoot, 'observability', 'trace-schema.yaml');
const args = process.argv.slice(2);
const dataPath = args[0] || path.join(repoRoot, 'samples', 'conformance', 'sample-traces.json');

if (!fs.existsSync(schemaPath)) {
  console.error(`Schema not found: ${schemaPath}`);
  process.exit(1);
}

if (!fs.existsSync(dataPath)) {
  console.error(`Data file not found: ${dataPath}`);
  process.exit(1);
}

const schema = readYaml(schemaPath);
const data = readJson(dataPath);

const ajv = new Ajv({ allErrors: true, strict: false });
addFormats(ajv);

const validate = ajv.compile({
  $id: 'TraceEvent',
  type: 'object',
  properties: schema.properties || {},
  required: schema.required || [],
  additionalProperties: true
});

const events = Array.isArray(data) ? data : [data];
let ok = true;
for (let i = 0; i < events.length; i++) {
  const ev = events[i];
  const valid = validate(ev);
  if (!valid) {
    ok = false;
    console.error(`Event #${i+1} failed schema validation:`);
    for (const err of validate.errors || []) {
      console.error(` - ${err.instancePath} ${err.message}`);
    }
  }
}

if (ok) {
  console.log(`✓ ${events.length} event(s) validated against trace schema`);
  process.exit(0);
} else {
  process.exit(1);
}

