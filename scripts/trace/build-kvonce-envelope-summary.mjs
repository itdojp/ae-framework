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
    domainSummaries: [],
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
    } else if (arg === '--domain-summary' && next) {
      options.domainSummaries.push(next);
      i += 1;
    } else if (arg === '--help' || arg === '-h') {
      console.log(`Usage: node scripts/trace/build-kvonce-envelope-summary.mjs [options]

Options:
  -o, --output <file>      Output JSON path (default: artifacts/kvonce-trace-summary.json)
  -d, --trace-dir <dir>    Base directory containing trace artifacts (default: hermetic-reports/trace)
  -s, --summary <file>     Conformance summary JSON (default: <trace-dir>/kvonce-conformance-summary.json)
      --cases <list>       Comma-separated case descriptors key[:label[:subdir]]
      --domain-summary <file>
                           Additional domain summary JSON (repeatable)
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

const parseCases = () => {
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
};

const cases = parseCases();

const readJsonSafe = (filePath) => {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    return null;
  }
};

const toStringArray = (value) => {
  if (!Array.isArray(value)) return [];
  return value
    .map((item) => (typeof item === 'string' ? item.trim() : ''))
    .filter(Boolean);
};

function normalizeDomainSummary(summary, sourcePath) {
  if (!summary || typeof summary !== 'object') return null;
  const defaultKey = path.basename(sourcePath, path.extname(sourcePath));
  const keyCandidate = typeof summary.key === 'string' ? summary.key.trim() : '';
  const key = keyCandidate || defaultKey;
  const labelCandidate = typeof summary.label === 'string' ? summary.label.trim() : '';
  const label = labelCandidate || key;
  const statusCandidate = typeof summary.status === 'string' ? summary.status.trim() : '';
  const status = statusCandidate || 'unknown';
  const issuesValue = summary.issues;
  let issues = 0;
  if (typeof issuesValue === 'number' && Number.isFinite(issuesValue)) {
    issues = issuesValue;
  } else if (Array.isArray(issuesValue)) {
    issues = issuesValue.length;
  }
  const traceIds = toStringArray(summary.traceIds);
  const tempoLinks = toStringArray(summary.tempoLinks);
  const artifacts = summary.artifacts && typeof summary.artifacts === 'object' ? summary.artifacts : null;
  const metrics = summary.metrics && typeof summary.metrics === 'object' ? summary.metrics : null;
  const notes = toStringArray(summary.notes);
  const entry = {
    key,
    label,
    status,
    issues,
    traceIds,
    tempoLinks,
  };
  if (artifacts && Object.keys(artifacts).length > 0) {
    entry.artifacts = artifacts;
  }
  if (metrics && Object.keys(metrics).length > 0) {
    entry.metrics = metrics;
  }
  if (notes.length > 0) {
    entry.notes = notes;
  }
  const sourceRelative = path.relative(process.cwd(), sourcePath);
  const meta = {
    key,
    label,
    status,
    source: sourceRelative,
  };
  if (traceIds.length > 0) {
    meta.traceIdCount = traceIds.length;
  }
  if (issues > 0) {
    meta.issues = issues;
  }
  return { entry, meta, traceIds, tempoLinks };
}


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

  if (fs.existsSync(reportPath)) {
    entry.validationPath = path.relative(process.cwd(), reportPath);
  }
  if (fs.existsSync(projectionPath)) {
    entry.projectionPath = path.relative(process.cwd(), projectionPath);
  }
  if (fs.existsSync(stateSequencePath)) {
    entry.stateSequencePath = path.relative(process.cwd(), stateSequencePath);
  }
  if (traceIds.length > 0) {
    entry.traceIds = traceIds;
  }
  if (tempoLinks.length > 0) {
    entry.tempoLinks = tempoLinks;
  }

  casesSummary.push(entry);
}

const summaryPath = options.summary
  ? path.resolve(options.summary)
  : path.join(traceDir, 'kvonce-conformance-summary.json');

const conformanceSummary = fs.existsSync(summaryPath) ? readJsonSafe(summaryPath) : null;
if (Array.isArray(conformanceSummary?.trace?.traceIds)) {
  for (const value of conformanceSummary.trace.traceIds) {
    if (typeof value === 'string' && value.trim()) {
      aggregateTraceIds.add(value.trim());
    }
  }
}
if (Array.isArray(conformanceSummary?.tempoLinks)) {
  for (const value of conformanceSummary.tempoLinks) {
    if (typeof value === 'string' && value.trim()) {
      aggregateTempoLinks.add(value.trim());
    }
  }
}

const domainEntries = casesSummary.map((entry) => {
  const status = entry.status ?? (entry.valid === true ? 'valid' : (entry.valid === false ? 'invalid' : 'unknown'));
  const artifacts = {};
  if (entry.validationPath) artifacts.validationPath = entry.validationPath;
  if (entry.projectionPath) artifacts.projectionPath = entry.projectionPath;
  if (entry.stateSequencePath) artifacts.stateSequencePath = entry.stateSequencePath;
  const metrics = {};
  if (entry.projectionStats?.eventCount !== undefined) metrics.eventCount = entry.projectionStats.eventCount;
  if (entry.projectionStats?.stateSequenceLength !== undefined) metrics.stateSequenceLength = entry.projectionStats.stateSequenceLength;
  return {
    key: entry.format,
    label: entry.label ?? entry.format,
    status,
    issues: entry.issueCount ?? 0,
    traceIds: Array.isArray(entry.traceIds) ? entry.traceIds : [],
    tempoLinks: Array.isArray(entry.tempoLinks) ? entry.tempoLinks : [],
    ...(Object.keys(artifacts).length > 0 ? { artifacts } : {}),
    ...(Object.keys(metrics).length > 0 ? { metrics } : {}),
  };
});

const domainSummaryMetadata = [];
for (const summaryPath of options.domainSummaries) {
  if (!summaryPath) continue;
  const directPath = path.resolve(summaryPath);
  const fallbackPath = path.resolve(traceDir, summaryPath);
  let resolved = null;
  if (fs.existsSync(directPath)) {
    resolved = directPath;
  } else if (fs.existsSync(fallbackPath)) {
    resolved = fallbackPath;
  }
  if (!resolved) {
    console.warn(`[trace] domain summary not found: ${summaryPath}`);
    continue;
  }
  const summaryData = readJsonSafe(resolved);
  if (!summaryData) {
    console.warn(`[trace] failed to parse domain summary: ${resolved}`);
    continue;
  }
  const normalized = normalizeDomainSummary(summaryData, resolved);
  if (!normalized) {
    console.warn(`[trace] invalid domain summary structure: ${resolved}`);
    continue;
  }
  const {
    entry,
    meta,
    traceIds: extraTraceIds = [],
    tempoLinks: extraTempoLinks = [],
  } = normalized;
  domainEntries.push(entry);
  extraTraceIds.forEach((value) => aggregateTraceIds.add(value));
  extraTempoLinks.forEach((value) => aggregateTempoLinks.add(value));
  domainSummaryMetadata.push(meta);
}

const aggregateTraceIdsArray = Array.from(aggregateTraceIds);
const aggregateTempoLinksArray = Array.from(aggregateTempoLinks);

const aggregate = {
  traceIds: aggregateTraceIdsArray,
  tempoLinks: aggregateTempoLinksArray,
  issues: domainEntries.reduce((total, domain) => total + (domain.issues ?? 0), 0),
};

const traceSummary = {
  ...(conformanceSummary?.trace ?? {}),
  domains: domainEntries,
  aggregate,
};
if (aggregateTraceIdsArray.length > 0) {
  traceSummary.traceIds = aggregateTraceIdsArray;
}
if (aggregateTempoLinksArray.length > 0) {
  traceSummary.tempoLinks = aggregateTempoLinksArray;
}

const output = {
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
  trace: traceSummary,
};

if (domainSummaryMetadata.length > 0) {
  output.domainSummaries = domainSummaryMetadata;
}

if (conformanceSummary) {
  const conformanceTrace = {
    ...(conformanceSummary.trace ?? {}),
    domains: domainEntries,
    traceIds: traceSummary.traceIds ?? [],
    tempoLinks: traceSummary.tempoLinks ?? [],
    aggregate,
  };
  output.conformance = {
    ...conformanceSummary,
    trace: conformanceTrace,
  };
}
if (aggregateTraceIdsArray.length > 0) {
  output.traceIds = aggregateTraceIdsArray;
}
if (aggregateTempoLinksArray.length > 0) {
  output.tempoLinks = aggregateTempoLinksArray;
}

const destDir = path.dirname(outputPath);
if (!fs.existsSync(destDir)) {
  fs.mkdirSync(destDir, { recursive: true });
}

fs.writeFileSync(outputPath, JSON.stringify(output, null, 2));
console.log(`[trace] wrote kvonce summary to ${outputPath}`);
