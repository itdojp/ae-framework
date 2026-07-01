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

function usage() {
  console.log(`Usage: node scripts/formal/trace-validate.mjs [options] [trace-file]

Options:
  --in, --input, --file <path>  Trace JSON file to validate (default: samples/conformance/sample-traces.json)
  -h, --help                   Show this help
`);
}

function requireNext(argv, index, optionName) {
  const next = argv[index + 1];
  if (!next || next === '--') {
    throw new Error(`${optionName} requires a trace file path`);
  }
  return next;
}

function parseArgs(argv) {
  const positional = [];
  let inputPath;

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }
    if (arg === '-h' || arg === '--help') {
      return { help: true };
    }
    if (arg === '--in' || arg === '--input' || arg === '--file') {
      inputPath = requireNext(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg.startsWith('--in=')) {
      inputPath = arg.slice('--in='.length);
      continue;
    }
    if (arg.startsWith('--input=')) {
      inputPath = arg.slice('--input='.length);
      continue;
    }
    if (arg.startsWith('--file=')) {
      inputPath = arg.slice('--file='.length);
      continue;
    }
    if (arg.startsWith('-')) {
      throw new Error(`Unknown option: ${arg}`);
    }
    positional.push(arg);
  }

  const optionInputProvided = Boolean(inputPath);
  if (!optionInputProvided && positional.length > 0) {
    inputPath = positional[0];
  }
  if (optionInputProvided && positional.length > 0) {
    throw new Error(`Unexpected extra trace file path: ${positional.join(', ')}`);
  }
  if (!optionInputProvided && positional.length > 1) {
    throw new Error(`Unexpected extra trace file path: ${positional.slice(1).join(', ')}`);
  }
  if (typeof inputPath === 'string' && inputPath.trim() === '') {
    throw new Error('Trace file path must be non-empty');
  }

  return {
    help: false,
    dataPath: path.resolve(repoRoot, inputPath || path.join('samples', 'conformance', 'sample-traces.json')),
  };
}

let dataPath;
try {
  const options = parseArgs(process.argv.slice(2));
  if (options.help) {
    usage();
    process.exit(0);
  }
  dataPath = options.dataPath;
} catch (error) {
  console.error(error instanceof Error ? error.message : String(error));
  process.exit(1);
}

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

const schemaConfig = {
  $id: 'TraceEvent',
  type: 'object',
  properties: schema.properties || {},
  required: schema.required || [],
  additionalProperties: true
};
if (schema.definitions) {
  schemaConfig.definitions = schema.definitions;
}
if (schema.$defs) {
  schemaConfig.$defs = schema.$defs;
}
const validate = ajv.compile(schemaConfig);

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
