#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { collectTraceIdsFromNdjson, buildTempoLinks } from './tempo-link-utils.mjs';

function parseArgs(argv) {
  const options = {
    traceDir: path.join('hermetic-reports', 'trace', 'inventory'),
    output: path.join('artifacts', 'trace', 'inventory-domain-summary.json'),
    key: 'inventory',
    label: 'Inventory',
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    switch (arg) {
      case '--trace-dir':
      case '-d':
        if (!next) {
          console.error('[inventory-domain-summary] missing value for --trace-dir');
          process.exit(1);
        }
        options.traceDir = next;
        i += 1;
        break;
      case '--output':
      case '-o':
        if (!next) {
          console.error('[inventory-domain-summary] missing value for --output');
          process.exit(1);
        }
        options.output = next;
        i += 1;
        break;
      case '--label':
        if (!next) {
          console.error('[inventory-domain-summary] missing value for --label');
          process.exit(1);
        }
        options.label = next;
        i += 1;
        break;
      case '--key':
        if (!next) {
          console.error('[inventory-domain-summary] missing value for --key');
          process.exit(1);
        }
        options.key = next;
        i += 1;
        break;
      case '--help':
      case '-h':
        console.log(`Usage: node scripts/trace/build-inventory-domain-summary.mjs [options]

Options:
  -d, --trace-dir <dir>   Directory containing inventory projection/validation artifacts (default: hermetic-reports/trace/inventory)
  -o, --output <file>     Output JSON path (default: artifacts/trace/inventory-domain-summary.json)
      --key <name>        Domain key (default: inventory)
      --label <label>     Domain label (default: Inventory)
  -h, --help              Show this message
`);
        process.exit(0);
        break;
      default:
        console.error(`[inventory-domain-summary] unknown argument: ${arg}`);
        process.exit(1);
    }
  }

  return options;
}

function readJsonSafe(file) {
  try {
    return JSON.parse(fs.readFileSync(file, 'utf8'));
  } catch (error) {
    return null;
  }
}

const options = parseArgs(process.argv);
const traceDir = path.resolve(options.traceDir);
const outputPath = path.resolve(options.output);

const projectionPath = path.join(traceDir, 'inventory-projection.json');
const validationPath = path.join(traceDir, 'inventory-validation.json');
const ndjsonPath = path.join(traceDir, 'inventory-events.ndjson');
const stateSequencePath = path.join(traceDir, 'projected', 'inventory-state-sequence.json');

const projection = readJsonSafe(projectionPath);
const validation = readJsonSafe(validationPath);

const projectionExists = Boolean(projection);
const validationExists = Boolean(validation);

const traceIds = Array.isArray(projection?.traceIds) && projection.traceIds.length > 0
  ? projection.traceIds
  : collectTraceIdsFromNdjson(fs.existsSync(ndjsonPath) ? ndjsonPath : null);

const tempoLinks = buildTempoLinks(traceIds);

let status = 'unknown';
if (validationExists) {
  status = validation.valid === true ? 'valid' : (validation.valid === false ? 'invalid' : 'unknown');
} else if (projectionExists) {
  status = 'generated';
}

const validationIssues = Array.isArray(validation?.issues) ? validation.issues : [];
const errorCount = validationIssues.filter((issue) => (issue?.severity ?? 'error') !== 'warning').length;

const artifacts = {};
if (fs.existsSync(validationPath)) artifacts.validationPath = path.relative(process.cwd(), validationPath);
if (fs.existsSync(projectionPath)) artifacts.projectionPath = path.relative(process.cwd(), projectionPath);
if (fs.existsSync(stateSequencePath)) artifacts.stateSequencePath = path.relative(process.cwd(), stateSequencePath);

const metrics = {};
if (typeof projection?.eventCount === 'number') metrics.eventCount = projection.eventCount;
if (typeof projection?.metrics?.stateSequenceLength === 'number') metrics.stateSequenceLength = projection.metrics.stateSequenceLength;
if (typeof validation?.metrics?.statesChecked === 'number') metrics.statesChecked = validation.metrics.statesChecked;
metrics.validationIssueCount = validationIssues.length;
metrics.validationErrorCount = errorCount;

const notes = [];
if (!projectionExists) notes.push('projection_missing');
if (!validationExists) notes.push('validation_missing');
if (traceIds.length === 0) notes.push('trace_ids_missing');

const summary = {
  key: options.key,
  label: options.label,
  status,
  issues: errorCount,
  traceIds,
};

if (tempoLinks.length > 0) {
  summary.tempoLinks = tempoLinks;
}
if (Object.keys(artifacts).length > 0) {
  summary.artifacts = artifacts;
}
if (Object.keys(metrics).length > 0) {
  summary.metrics = metrics;
}
if (notes.length > 0) {
  summary.notes = notes;
}

fs.mkdirSync(path.dirname(outputPath), { recursive: true });
fs.writeFileSync(outputPath, JSON.stringify(summary, null, 2));
console.log(`[inventory-domain-summary] wrote summary to ${outputPath}`);
