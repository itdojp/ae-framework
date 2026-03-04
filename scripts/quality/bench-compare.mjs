#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const DEFAULT_OUTPUT_JSON = 'artifacts/bench-compare.json';
const DEFAULT_OUTPUT_MD = 'artifacts/bench-compare.md';

function printUsage() {
  process.stdout.write(`Usage: node scripts/quality/bench-compare.mjs --baseline <path> --candidate <name=path> [--candidate <name=path> ...] [options]

Options:
  --baseline <path>               baseline bench.json path (benchmark-report/v1)
  --candidate <name=path>         candidate label and bench.json path (repeatable)
  --out-json <path>               output JSON path (default: ${DEFAULT_OUTPUT_JSON})
  --out-md <path>                 output Markdown path (default: ${DEFAULT_OUTPUT_MD})
  --fail-on-threshold-breach      exit code 1 when any candidate fails required thresholds
  --help                          show this message
`);
}

function parseArgs(argv) {
  const options = {
    baselinePath: '',
    candidates: [],
    outJsonPath: DEFAULT_OUTPUT_JSON,
    outMdPath: DEFAULT_OUTPUT_MD,
    failOnThresholdBreach: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') {
      printUsage();
      process.exit(0);
    }
    if (arg === '--baseline') {
      const next = argv[index + 1];
      if (!next) throw new Error('--baseline requires a value');
      options.baselinePath = next;
      index += 1;
      continue;
    }
    if (arg === '--candidate') {
      const next = argv[index + 1];
      if (!next) throw new Error('--candidate requires a value');
      options.candidates.push(next);
      index += 1;
      continue;
    }
    if (arg === '--out-json') {
      const next = argv[index + 1];
      if (!next) throw new Error('--out-json requires a value');
      options.outJsonPath = next;
      index += 1;
      continue;
    }
    if (arg === '--out-md') {
      const next = argv[index + 1];
      if (!next) throw new Error('--out-md requires a value');
      options.outMdPath = next;
      index += 1;
      continue;
    }
    if (arg === '--fail-on-threshold-breach') {
      options.failOnThresholdBreach = true;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (!options.baselinePath) {
    throw new Error('--baseline is required');
  }
  if (options.candidates.length === 0) {
    throw new Error('at least one --candidate is required');
  }

  return {
    baselinePath: path.resolve(options.baselinePath),
    candidates: options.candidates.map(parseCandidateArg),
    outJsonPath: path.resolve(options.outJsonPath),
    outMdPath: path.resolve(options.outMdPath),
    failOnThresholdBreach: options.failOnThresholdBreach,
  };
}

function parseCandidateArg(raw) {
  const [name, filePath] = String(raw).split('=');
  const normalizedName = String(name || '').trim();
  const normalizedPath = String(filePath || '').trim();
  if (!normalizedName || !normalizedPath) {
    throw new Error(`invalid --candidate format: ${raw} (expected <name=path>)`);
  }
  return {
    name: normalizedName,
    path: path.resolve(normalizedPath),
  };
}

function readJsonFile(filePath) {
  const raw = fs.readFileSync(filePath, 'utf8');
  return JSON.parse(raw);
}

function assertNonNegativeFiniteNumber(value, label) {
  if (typeof value !== 'number' || !Number.isFinite(value) || value < 0) {
    throw new Error(`${label} must be a non-negative finite number`);
  }
  return value;
}

function readBenchmarkReport(filePath) {
  if (!fs.existsSync(filePath)) {
    throw new Error(`benchmark report not found: ${filePath}`);
  }

  const report = readJsonFile(filePath);
  if (report?.schemaVersion !== 'benchmark-report/v1') {
    throw new Error(`unsupported schemaVersion at ${filePath}: ${String(report?.schemaVersion || '')}`);
  }

  const summary = Array.isArray(report.summary) ? report.summary : [];
  const throughputHz = summary.reduce((sum, task) => {
    const hz = Number(task?.hz);
    return Number.isFinite(hz) && hz > 0 ? sum + hz : sum;
  }, 0);
  const normalizedThroughputHz = throughputHz > 0 ? throughputHz : null;

  const metrics = {
    p95: assertNonNegativeFiniteNumber(report?.metrics?.p95, `${filePath}: metrics.p95`),
    errorRate: assertNonNegativeFiniteNumber(report?.metrics?.errorRate, `${filePath}: metrics.errorRate`),
    coldStartMs: assertNonNegativeFiniteNumber(report?.metrics?.coldStartMs, `${filePath}: metrics.coldStartMs`),
    peakRssMb: assertNonNegativeFiniteNumber(report?.metrics?.peakRssMb, `${filePath}: metrics.peakRssMb`),
  };

  return {
    path: filePath,
    metrics,
    throughputHz: normalizedThroughputHz,
    taskCount: summary.length,
  };
}

function round(value, digits = 4) {
  return Number(value.toFixed(digits));
}

function ratio(candidateValue, baselineValue) {
  if (baselineValue <= 0) return null;
  return candidateValue / baselineValue;
}

function evaluateCandidate(candidate, baseline) {
  const p95Ratio = ratio(candidate.metrics.p95, baseline.metrics.p95);
  const throughputRatio = candidate.throughputHz !== null && baseline.throughputHz !== null
    ? ratio(candidate.throughputHz, baseline.throughputHz)
    : null;
  const coldStartRatio = ratio(candidate.metrics.coldStartMs, baseline.metrics.coldStartMs);
  const peakRssRatio = ratio(candidate.metrics.peakRssMb, baseline.metrics.peakRssMb);
  const errorRateLimit = Math.max(0.5, baseline.metrics.errorRate + 0.2);

  const checks = {
    p95: p95Ratio !== null && p95Ratio <= 0.85,
    throughput: throughputRatio !== null && throughputRatio >= 1.2,
    errorRate: candidate.metrics.errorRate <= errorRateLimit,
    peakRss: peakRssRatio !== null && peakRssRatio <= 1.15,
    coldStartReference: coldStartRatio !== null && coldStartRatio <= 1.1,
  };

  const overallPass = checks.p95 && checks.throughput && checks.errorRate && checks.peakRss;

  return {
    name: candidate.name,
    path: candidate.path,
    metrics: candidate.metrics,
    throughputHz: candidate.throughputHz,
    comparison: {
      p95Ratio: p95Ratio === null ? null : round(p95Ratio),
      throughputRatio: throughputRatio === null ? null : round(throughputRatio),
      coldStartRatio: coldStartRatio === null ? null : round(coldStartRatio),
      peakRssRatio: peakRssRatio === null ? null : round(peakRssRatio),
      errorRateLimit: round(errorRateLimit),
      errorRateDeltaPt: round(candidate.metrics.errorRate - baseline.metrics.errorRate),
    },
    checks,
    overall: overallPass ? 'pass' : 'fail',
  };
}

function ensureParentDir(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function fmtNumber(value, digits = 3) {
  if (value === null || value === undefined) return 'n/a';
  return Number(value).toFixed(digits);
}

function renderMarkdown(result) {
  const lines = [
    '# Bench Comparison Report',
    '',
    `- Generated: ${result.generatedAt}`,
    `- Baseline: ${result.baseline.path}`,
    '',
    '| candidate | overall | p95 ratio | throughput ratio | error rate(%) | error limit(%) | peak RSS ratio | cold start ratio |',
    '|---|---|---:|---:|---:|---:|---:|---:|',
  ];

  for (const candidate of result.candidates) {
    lines.push(
      `| ${candidate.name} | ${candidate.overall.toUpperCase()} | ${fmtNumber(candidate.comparison.p95Ratio, 4)} | ${fmtNumber(candidate.comparison.throughputRatio, 4)} | ${fmtNumber(candidate.metrics.errorRate, 2)} | ${fmtNumber(candidate.comparison.errorRateLimit, 2)} | ${fmtNumber(candidate.comparison.peakRssRatio, 4)} | ${fmtNumber(candidate.comparison.coldStartRatio, 4)} |`,
    );
  }

  lines.push(
    '',
    '## Required checks',
    '- p95 ratio <= 0.85',
    '- throughput ratio >= 1.20',
    '- error rate <= max(0.5, baseline + 0.2pt)',
    '- peak RSS ratio <= 1.15',
    '',
    '## Reference check',
    '- cold start ratio <= 1.10',
    '',
  );
  return lines.join('\n');
}

function main() {
  const options = parseArgs(process.argv.slice(2));
  const baseline = readBenchmarkReport(options.baselinePath);
  const candidates = options.candidates.map((candidate) => {
    const report = readBenchmarkReport(candidate.path);
    return evaluateCandidate({ ...candidate, ...report }, baseline);
  });

  const result = {
    schemaVersion: 'bench-compare/v1',
    generatedAt: new Date().toISOString(),
    baseline: {
      path: baseline.path,
      metrics: baseline.metrics,
      throughputHz: baseline.throughputHz,
      taskCount: baseline.taskCount,
    },
    candidates,
  };

  ensureParentDir(options.outJsonPath);
  ensureParentDir(options.outMdPath);
  fs.writeFileSync(options.outJsonPath, `${JSON.stringify(result, null, 2)}\n`, 'utf8');
  fs.writeFileSync(options.outMdPath, renderMarkdown(result), 'utf8');

  process.stdout.write(`[bench:compare] wrote ${options.outJsonPath}\n`);
  process.stdout.write(`[bench:compare] wrote ${options.outMdPath}\n`);

  if (options.failOnThresholdBreach && candidates.some((candidate) => candidate.overall !== 'pass')) {
    process.exitCode = 1;
  }
}

try {
  main();
} catch (error) {
  const message = error instanceof Error ? error.message : String(error);
  process.stderr.write(`[bench:compare] fatal: ${message}\n`);
  process.exitCode = 1;
}
