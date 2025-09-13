#!/usr/bin/env node
// Minimal conformance check: validate trace schema and basic invariants
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
function writeJson(p,obj){ fs.mkdirSync(path.dirname(p),{recursive:true}); fs.writeFileSync(p, JSON.stringify(obj,null,2)); }

const schemaPath = path.join(repoRoot, 'observability', 'trace-schema.yaml');
const dataPath = process.argv[2] || path.join(repoRoot, 'samples', 'conformance', 'sample-traces.json');
const outDir = path.join(repoRoot, 'hermetic-reports', 'conformance');
const outFile = path.join(outDir, 'summary.json');

if (!fs.existsSync(schemaPath)) {
  console.error(`Schema not found: ${schemaPath}`);
  process.exit(0); // non-blocking
}
if (!fs.existsSync(dataPath)) {
  console.error(`Data not found: ${dataPath}`);
  process.exit(0);
}

const schema = readYaml(schemaPath);
const data = readJson(dataPath);
const events = Array.isArray(data) ? data : [data];

const ajv = new Ajv({ allErrors: true, strict: false });
addFormats(ajv);
const validate = ajv.compile({
  $id: 'TraceEvent',
  type: 'object',
  properties: schema.properties || {},
  required: schema.required || [],
  additionalProperties: true
});

let schemaErrors = [];
let invariantViolations = [];

for (let i = 0; i < events.length; i++) {
  const ev = events[i];
  const ok = validate(ev);
  if (!ok) {
    for (const err of validate.errors || []) {
      schemaErrors.push({ index: i, path: err.instancePath, message: err.message });
    }
  }
  const st = ev && ev.state;
  if (st && typeof st === 'object') {
    const hasOnHand = typeof st.onHand === 'number';
    const hasAllocated = typeof st.allocated === 'number';
    if (hasOnHand && st.onHand < 0) {
      invariantViolations.push({ index: i, invariant: 'onHand >= 0', actual: st.onHand });
    }
    if (hasOnHand && hasAllocated && st.allocated > st.onHand) {
      invariantViolations.push({ index: i, invariant: 'allocated <= onHand', actual: { allocated: st.allocated, onHand: st.onHand } });
    }
  }
}

const summary = {
  input: path.relative(repoRoot, dataPath),
  events: events.length,
  schemaErrors: schemaErrors.length,
  invariantViolations: invariantViolations.length,
  timestamp: new Date().toISOString(),
  details: { schemaErrors, invariantViolations }
};

writeJson(outFile, summary);
console.log(`Conformance summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- events=${summary.events} schemaErrors=${summary.schemaErrors} invariantViolations=${summary.invariantViolations}`);

// Non-blocking (label-gated workflow); always exit 0
process.exit(0);
