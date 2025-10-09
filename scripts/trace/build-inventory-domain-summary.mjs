#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const SEVERITY_ERROR = 'error';
const SEVERITY_WARNING = 'warning';

function fallbackCollectTraceIdsFromNdjson(ndjsonPath) {
  if (!ndjsonPath || !fs.existsSync(ndjsonPath)) return [];
  const ids = new Set();
  const content = fs.readFileSync(ndjsonPath, 'utf8');
  for (const line of content.split(/\r?\n/)) {
    if (!line.trim()) continue;
    try {
      const event = JSON.parse(line);
      const value = event && typeof event.traceId === 'string' ? event.traceId.trim() : '';
      if (value) ids.add(value);
    } catch (error) {
      // ignore malformed line
    }
  }
  return Array.from(ids);
}

function fallbackBuildTempoLinks(traceIds, template = process.env.REPORT_ENVELOPE_TEMPO_LINK_TEMPLATE) {
  if (!Array.isArray(traceIds) || traceIds.length === 0) return [];
  const resolved = template?.trim();
  if (!resolved) return [];
  return traceIds.map((id) => {
    const encoded = encodeURIComponent(id);
    if (resolved.includes('{traceId}')) {
      return resolved.replace('{traceId}', encoded);
    }
    const separator = resolved.includes('?') ? '&' : '?';
    return `${resolved}${separator}traceId=${encoded}`;
  });
}

async function loadTempoUtils() {
  const fallbacks = {
    collectTraceIdsFromNdjson: fallbackCollectTraceIdsFromNdjson,
    buildTempoLinks: fallbackBuildTempoLinks,
  };
  try {
    const utils = await import('./tempo-link-utils.mjs');
    return {
      collectTraceIdsFromNdjson: typeof utils.collectTraceIdsFromNdjson === 'function' ? utils.collectTraceIdsFromNdjson : fallbacks.collectTraceIdsFromNdjson,
      buildTempoLinks: typeof utils.buildTempoLinks === 'function' ? utils.buildTempoLinks : fallbacks.buildTempoLinks,
    };
  } catch (error) {
    return fallbacks;
  }
}

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

async function main() {
  const { collectTraceIdsFromNdjson, buildTempoLinks } = await loadTempoUtils();
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
  const ndjsonExists = fs.existsSync(ndjsonPath);

  const traceIds = Array.isArray(projection?.traceIds) && projection.traceIds.length > 0
    ? projection.traceIds
    : (ndjsonExists ? collectTraceIdsFromNdjson(ndjsonPath) : []);

  const tempoLinks = buildTempoLinks(traceIds);

  let status = 'unknown';
  if (validationExists) {
    status = validation.valid === true ? 'valid' : (validation.valid === false ? 'invalid' : 'unknown');
  } else if (projectionExists) {
    status = 'generated';
  }

  const validationIssues = Array.isArray(validation?.issues) ? validation.issues : [];
  const errorCount = validationIssues.filter((issue) => (issue?.severity ?? SEVERITY_ERROR) !== SEVERITY_WARNING).length;

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
}

main().catch((error) => {
  console.error(`[inventory-domain-summary] fatal: ${error.message}`);
  process.exit(1);
});
