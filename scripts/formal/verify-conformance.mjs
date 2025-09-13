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

function parseArgs(argv) {
  const args = { _: [] };
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--help' || a === '-h') args.help = true;
    else if ((a === '--in' || a === '-i') && argv[i+1]) { args.in = argv[++i]; }
    else if (a.startsWith('--in=')) { args.in = a.slice(5); }
    else if (a === '--out' && argv[i+1]) { args.out = argv[++i]; }
    else if (a.startsWith('--out=')) { args.out = a.slice(6); }
    else if (a === '--schema' && argv[i+1]) { args.schema = argv[++i]; }
    else if (a.startsWith('--schema=')) { args.schema = a.slice(9); }
    else if (a === '--disable-invariants' && argv[i+1]) { args.disable = argv[++i]; }
    else if (a.startsWith('--disable-invariants=')) { args.disable = a.slice(21); }
    else if (a === '--onhand-min' && argv[i+1]) { args.onhandMin = argv[++i]; }
    else if (a.startsWith('--onhand-min=')) { args.onhandMin = a.slice(13); }
    else { args._.push(a); }
  }
  return args;
}

const args = parseArgs(process.argv);

if (args.help) {
  console.log(`Usage: node scripts/formal/verify-conformance.mjs [options]\n\nOptions:\n  -i, --in <file>                Input events JSON (default: samples/conformance/sample-traces.json)\n  --schema <file>                Trace schema YAML (default: observability/trace-schema.yaml)\n  --out <file>                   Output summary JSON (default: hermetic-reports/conformance/summary.json)\n  --disable-invariants <list>    Comma-separated invariants to disable (allocated_le_onhand,onhand_min)\n  --onhand-min <number>          Minimum onHand for onhand_min invariant (default: 0)\n  -h, --help                     Show this help\n`);
  process.exit(0);
}

const schemaPath = path.resolve(repoRoot, args.schema || path.join('observability', 'trace-schema.yaml'));
const dataPath = path.resolve(repoRoot, args.in || path.join('samples', 'conformance', 'sample-traces.json'));
const outFile = path.resolve(repoRoot, args.out || path.join('hermetic-reports', 'conformance', 'summary.json'));
const outDir = path.dirname(outFile);

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
const byType = { onhand_min: 0, allocated_le_onhand: 0 };
const disable = new Set((args.disable || '').split(',').map(s=>s.trim()).filter(Boolean));
const onhandMin = Number.isFinite(Number(args.onhandMin)) ? Number(args.onhandMin) : 0;

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
    if (!disable.has('onhand_min') && hasOnHand && st.onHand < onhandMin) {
      invariantViolations.push({ index: i, type: 'onhand_min', invariant: `onHand >= ${onhandMin}`, actual: st.onHand });
      byType.onhand_min++;
    }
    if (!disable.has('allocated_le_onhand') && hasOnHand && hasAllocated && st.allocated > st.onHand) {
      invariantViolations.push({ index: i, type: 'allocated_le_onhand', invariant: 'allocated <= onHand', actual: { allocated: st.allocated, onHand: st.onHand } });
      byType.allocated_le_onhand++;
    }
  }
}

const totalEvents = events.length || 0;
const invCount = invariantViolations.length;
const violationRate = totalEvents > 0 ? +(invCount / totalEvents).toFixed(3) : 0;
const summary = {
  input: path.relative(repoRoot, dataPath),
  events: totalEvents,
  schemaErrors: schemaErrors.length,
  invariantViolations: invCount,
  violationRate,
  timestamp: new Date().toISOString(),
  firstInvariantViolation: invariantViolations[0] || null,
  firstSchemaError: schemaErrors[0] || null,
  byType,
  details: { schemaErrors, invariantViolations, options: { disable: Array.from(disable), onhandMin } }
};

writeJson(outFile, summary);
console.log(`Conformance summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- input=${path.relative(repoRoot, dataPath)} schema=${path.relative(repoRoot, schemaPath)}`);
console.log(`- events=${summary.events} schemaErrors=${summary.schemaErrors} invariantViolations=${summary.invariantViolations}`);
if (args.disable || args.onhandMin !== undefined) {
  const disableList = (args.disable || '').split(',').map(s=>s.trim()).filter(Boolean).join(',') || 'none';
  console.log(`- options: disable=[${disableList}] onhandMin=${onhandMin}`);
}

// Non-blocking (label-gated workflow); always exit 0
process.exit(0);
