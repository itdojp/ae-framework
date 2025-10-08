#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { collectTraceIdsFromNdjson, buildTempoLinks } from './tempo-link-utils.mjs';

function parseArgs(argv) {
  const options = {
    output: 'artifacts/kvonce-trace-summary.json',
    traceDir: path.join('hermetic-reports', 'trace'),
    summary: null,
    cases: null,
  };
  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if ((arg === '--output' || arg === '-o') && next) {
      options.output = next;
      i += 1;
    } else if ((arg === '--trace-dir' || arg === '-d') && next) {
      options.traceDir = next;
      i += 1;
    } else if ((arg === '--summary' || arg === '-s') && next) {
      options.summary = next;
      i += 1;
    } else if (arg === '--cases' && next) {
      options.cases = next;
      i += 1;
    } else if (arg === '--help' || arg === '-h') {
      console.log(`Usage: node scripts/trace/build-kvonce-envelope-summary.mjs [options]

Options:
  -o, --output <file>      Output JSON path (default: artifacts/kvonce-trace-summary.json)
  -d, --trace-dir <dir>    Base directory containing trace artifacts (default: hermetic-reports/trace)
  -s, --summary <file>     Conformance summary JSON (default: <trace-dir>/kvonce-conformance-summary.json)
      --cases <list>       Comma-separated case descriptors key[:label[:subdir]]
  -h, --help               Show this message
`);
      process.exit(0);
    }
  }
  return options;
}

const options = parseArgs(process.argv);
const outputPath = path.resolve(options.output);
const traceDir = path.resolve(options.traceDir);

const defaultCases = [
  { key: 'current', label: 'Current run', dir: traceDir },
  { key: 'otlp', label: 'OTLP payload', dir: path.join(traceDir, 'otlp') },
  { key: 'ndjson', label: 'NDJSON sample', dir: path.join(traceDir, 'ndjson') },
];

function parseCases() {
  if (!options.cases) return defaultCases;
  const entries = [];
  for (const chunk of options.cases.split(',')) {
    const trimmed = chunk.trim();
    if (!trimmed) continue;
    const [key, label, subdir] = trimmed.split(':');
    if (!key) continue;
    const dir = subdir ? path.join(traceDir, subdir) : (key === 'current' ? traceDir : path.join(traceDir, key));
    entries.push({ key, label: label ?? key, dir });
  }
  return entries.length > 0 ? entries : defaultCases;
}

function readJsonSafe(filePath) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    return null;
  }
}

const cases = parseCases();
const metadata = readJsonSafe(path.join(traceDir, 'kvonce-payload-metadata.json')) ?? {};
const casesSummary = [];
const aggregateTraceIds = new Set();
const aggregateTempoLinks = new Set();

for (const item of cases) {
  if (!item?.dir) continue;
  const reportPath = path.join(item.dir, 'kvonce-validation.json');
  const projectionPath = path.join(item.dir, 'kvonce-projection.json');
  const stateSequencePath = path.join(item.dir, 'projected', 'kvonce-state-sequence.json');
  const ndjsonPath = path.join(item.dir, 'kvonce-events.ndjson');

  const validation = readJsonSafe(reportPath);
  const projection = readJsonSafe(projectionPath);

  if (!validation) {
    casesSummary.push({
      format: item.key,
      label: item.label ?? item.key,
      status: 'missing',
      issues: [],
      note: 'validation file missing',
    });
    continue;
  }

  const issues = Array.isArray(validation.issues) ? validation.issues : [];
  const trimmedIssues = issues.slice(0, 10).map((issue) => ({
    type: issue.type ?? 'unknown',
    key: issue.key ?? 'unknown',
    message: issue.message ?? '',
  }));
  const projectionStats = projection?.stats ?? undefined;
  const traceIds = collectTraceIdsFromNdjson(ndjsonPath);
  traceIds.forEach((value) => aggregateTraceIds.add(value));
  const tempoLinks = buildTempoLinks(traceIds);
  tempoLinks.forEach((value) => aggregateTempoLinks.add(value));

  const entry = {
    format: item.key,
    label: item.label ?? item.key,
    valid: Boolean(validation.valid),
    issueCount: issues.length,
    issues: trimmedIssues,
    projectionStats,
  };

  if (fs.existsSync(reportPath)) entry.validationPath = path.relative(process.cwd(), reportPath);
  if (fs.existsSync(projectionPath)) entry.projectionPath = path.relative(process.cwd(), projectionPath);
  if (fs.existsSync(stateSequencePath)) entry.stateSequencePath = path.relative(process.cwd(), stateSequencePath);
  if (traceIds.length > 0) entry.traceIds = traceIds;
  if (tempoLinks.length > 0) entry.tempoLinks = tempoLinks;

  casesSummary.push(entry);
}

const summaryPath = options.summary
  ? path.resolve(options.summary)
  : path.join(traceDir, 'kvonce-conformance-summary.json');

const conformanceSummary = fs.existsSync(summaryPath) ? readJsonSafe(summaryPath) : null;
if (Array.isArray(conformanceSummary?.trace?.traceIds)) {
  for (const value of conformanceSummary.trace.traceIds) {
    if (typeof value === 'string' && value.trim()) aggregateTraceIds.add(value.trim());
  }
}
if (Array.isArray(conformanceSummary?.tempoLinks)) {
  for (const value of conformanceSummary.tempoLinks) {
    if (typeof value === 'string' && value.trim()) aggregateTempoLinks.add(value.trim());
  }
}

const summary = {
  schemaVersion: '1.0.0',
  generatedAt: new Date().toISOString(),
  traceDir: path.relative(process.cwd(), traceDir),
  payloadMetadata: {
    sourceType: metadata.sourceType ?? null,
    sourceDetail: metadata.sourceDetail ?? null,
    sha256: metadata.sha256 ?? null,
    sizeBytes: metadata.sizeBytes ?? null,
  },
  cases: casesSummary,
};

if (conformanceSummary) {
  summary.conformance = conformanceSummary;
}
if (aggregateTraceIds.size > 0) {
  summary.traceIds = Array.from(aggregateTraceIds);
}
if (aggregateTempoLinks.size > 0) {
  summary.tempoLinks = Array.from(aggregateTempoLinks);
}

const destDir = path.dirname(outputPath);
if (!fs.existsSync(destDir)) {
  fs.mkdirSync(destDir, { recursive: true });
}

fs.writeFileSync(outputPath, JSON.stringify(summary, null, 2));
console.log(`[trace] wrote kvonce summary to ${outputPath}`);
