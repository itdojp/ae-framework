#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const DEFAULT_OUTPUT_JSON = 'artifacts/bench-compare.json';
const DEFAULT_OUTPUT_MD = 'artifacts/bench-compare.md';

function printUsage() {
  process.stdout.write(`Usage: node scripts/quality/bench-compare.mjs --baseline <path[,path...]> --candidate <name=path[,path...]> [--candidate <name=path[,path...]> ...] [options]

Options:
  --baseline <path[,path...]>     baseline bench.json path(s) (benchmark-report/v1)
  --candidate <name=path[,path...]> candidate label and bench.json path(s) (repeatable)
  --out-json <path>               output JSON path (default: ${DEFAULT_OUTPUT_JSON})
  --out-md <path>                 output Markdown path (default: ${DEFAULT_OUTPUT_MD})
  --fail-on-threshold-breach      exit code 1 when any candidate fails required thresholds
  --help                          show this message
`);
}

function parsePathList(rawValue, label) {
  const paths = String(rawValue || '')
    .split(',')
    .map((entry) => entry.trim())
    .filter((entry) => entry.length > 0);
  if (paths.length === 0) {
    throw new Error(`${label} requires at least one path`);
  }
  return paths.map((entry) => path.resolve(entry));
}

function parseArgs(argv) {
  const options = {
    baseline: '',
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
      options.baseline = next;
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

  if (!options.baseline) {
    throw new Error('--baseline is required');
  }
  if (options.candidates.length === 0) {
    throw new Error('at least one --candidate is required');
  }

  return {
    baselinePaths: parsePathList(options.baseline, '--baseline'),
    candidates: options.candidates.map(parseCandidateArg),
    outJsonPath: path.resolve(options.outJsonPath),
    outMdPath: path.resolve(options.outMdPath),
    failOnThresholdBreach: options.failOnThresholdBreach,
  };
}

function parseCandidateArg(raw) {
  const [name, ...rest] = String(raw).split('=');
  const normalizedName = String(name || '').trim();
  const value = rest.join('=').trim();
  if (!normalizedName || !value) {
    throw new Error(`invalid --candidate format: ${raw} (expected <name=path[,path...]>)`);
  }
  return {
    name: normalizedName,
    paths: parsePathList(value, `--candidate ${normalizedName}`),
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

function assertPercentage(value, label) {
  const normalized = assertNonNegativeFiniteNumber(value, label);
  if (normalized > 100) {
    throw new Error(`${label} must be <= 100`);
  }
  return normalized;
}

function readBenchmarkReport(filePath) {
  if (!fs.existsSync(filePath)) {
    throw new Error(`benchmark report not found: ${filePath}`);
  }

  const report = readJsonFile(filePath);
  if (report?.schemaVersion !== 'benchmark-report/v1') {
    throw new Error(`unsupported schemaVersion at ${filePath}: ${String(report?.schemaVersion || '')}`);
  }

  if (!Array.isArray(report.summary) || report.summary.length === 0) {
    throw new Error(`${filePath}: summary must be a non-empty array`);
  }
  const taskIdentities = report.summary.map((task, index) => {
    const normalizedName = typeof task?.name === 'string' ? task.name.trim() : '';
    return normalizedName.length > 0 ? normalizedName : `#${index + 1}`;
  });
  const throughputHz = report.summary.reduce((sum, task, index) => {
    const hz = Number(task?.hz);
    if (!Number.isFinite(hz) || hz <= 0) {
      throw new Error(`${filePath}: summary[${index}].hz must be a positive finite number`);
    }
    return sum + hz;
  }, 0);

  const metrics = {
    p95: assertNonNegativeFiniteNumber(report?.metrics?.p95, `${filePath}: metrics.p95`),
    errorRate: assertPercentage(report?.metrics?.errorRate, `${filePath}: metrics.errorRate`),
    coldStartMs: assertNonNegativeFiniteNumber(report?.metrics?.coldStartMs, `${filePath}: metrics.coldStartMs`),
    peakRssMb: assertNonNegativeFiniteNumber(report?.metrics?.peakRssMb, `${filePath}: metrics.peakRssMb`),
  };

  return {
    path: filePath,
    metrics,
    throughputHz,
    taskCount: report.summary.length,
    taskIdentities,
  };
}

function round(value, digits = 4) {
  return Number(value.toFixed(digits));
}

function median(values) {
  if (!Array.isArray(values) || values.length === 0) {
    throw new Error('median requires at least one numeric value');
  }
  const sorted = [...values].sort((left, right) => left - right);
  const middle = Math.floor(sorted.length / 2);
  if (sorted.length % 2 === 0) {
    return (sorted[middle - 1] + sorted[middle]) / 2;
  }
  return sorted[middle];
}

function standardDeviation(values) {
  if (!Array.isArray(values) || values.length === 0) {
    throw new Error('standardDeviation requires at least one numeric value');
  }
  if (values.length === 1) {
    return 0;
  }
  const mean = values.reduce((sum, value) => sum + value, 0) / values.length;
  const variance = values.reduce((sum, value) => {
    const diff = value - mean;
    return sum + (diff * diff);
  }, 0) / values.length;
  return Math.sqrt(variance);
}

function coefficientOfVariation(values) {
  if (!Array.isArray(values) || values.length < 2) {
    return null;
  }
  const mean = values.reduce((sum, value) => sum + value, 0) / values.length;
  if (mean <= 0) {
    return null;
  }
  return standardDeviation(values) / mean;
}

function assertConsistentRunShape(reports) {
  if (!Array.isArray(reports) || reports.length <= 1) {
    return;
  }
  const baseline = reports[0];
  const baselineTasks = [...baseline.taskIdentities].sort();

  for (const report of reports.slice(1)) {
    if (report.taskCount !== baseline.taskCount) {
      throw new Error(
        `inconsistent summary task count across runs: expected ${baseline.taskCount} (${baseline.path}), got ${report.taskCount} (${report.path})`,
      );
    }

    const reportTasks = [...report.taskIdentities].sort();
    const sameTasks = reportTasks.length === baselineTasks.length
      && reportTasks.every((task, index) => task === baselineTasks[index]);
    if (!sameTasks) {
      throw new Error(
        `inconsistent summary task identities across runs: expected [${baselineTasks.join(', ')}] (${baseline.path}), got [${reportTasks.join(', ')}] (${report.path})`,
      );
    }
  }
}

function aggregateBenchmarkRuns(reports) {
  if (!Array.isArray(reports) || reports.length === 0) {
    throw new Error('at least one benchmark report is required');
  }
  assertConsistentRunShape(reports);

  const p95Values = reports.map((report) => report.metrics.p95);
  const errorRateValues = reports.map((report) => report.metrics.errorRate);
  const coldStartValues = reports.map((report) => report.metrics.coldStartMs);
  const peakRssValues = reports.map((report) => report.metrics.peakRssMb);
  const throughputValues = reports.map((report) => report.throughputHz);

  return {
    paths: reports.map((report) => report.path),
    path: reports[0]?.path || '',
    runCount: reports.length,
    taskCount: reports[0]?.taskCount || 0,
    metrics: {
      p95: round(median(p95Values), 4),
      errorRate: round(median(errorRateValues), 4),
      coldStartMs: round(median(coldStartValues), 4),
      peakRssMb: round(median(peakRssValues), 4),
    },
    throughputHz: round(median(throughputValues), 4),
    reproducibility: {
      p95Cv: roundOrNull(coefficientOfVariation(p95Values), 4),
      throughputCv: roundOrNull(coefficientOfVariation(throughputValues), 4),
    },
  };
}

function roundOrNull(value, digits = 4) {
  if (value === null || value === undefined) {
    return null;
  }
  return round(value, digits);
}

function ratio(candidateValue, baselineValue) {
  if (baselineValue <= 0) return null;
  return candidateValue / baselineValue;
}

function upperBoundCheck(value, threshold) {
  if (value === null) return true;
  return value <= threshold;
}

function lowerBoundCheck(value, threshold) {
  if (value === null) return true;
  return value >= threshold;
}

function evaluateCandidate(candidate, baseline) {
  const p95Ratio = ratio(candidate.metrics.p95, baseline.metrics.p95);
  const throughputRatio = ratio(candidate.throughputHz, baseline.throughputHz);
  const coldStartRatio = ratio(candidate.metrics.coldStartMs, baseline.metrics.coldStartMs);
  const peakRssRatio = ratio(candidate.metrics.peakRssMb, baseline.metrics.peakRssMb);
  const errorRateLimit = Math.max(0.5, baseline.metrics.errorRate + 0.2);

  const checks = {
    p95: upperBoundCheck(p95Ratio, 0.85),
    throughput: lowerBoundCheck(throughputRatio, 1.2),
    errorRate: candidate.metrics.errorRate <= errorRateLimit,
    peakRss: upperBoundCheck(peakRssRatio, 1.15),
    coldStartReference: upperBoundCheck(coldStartRatio, 1.1),
    p95Cv: upperBoundCheck(candidate.reproducibility.p95Cv, 0.05),
    throughputCv: upperBoundCheck(candidate.reproducibility.throughputCv, 0.05),
  };

  const overallPass = checks.p95
    && checks.throughput
    && checks.errorRate
    && checks.peakRss
    && checks.p95Cv
    && checks.throughputCv;

  return {
    name: candidate.name,
    path: candidate.path,
    paths: candidate.paths,
    runCount: candidate.runCount,
    metrics: candidate.metrics,
    throughputHz: candidate.throughputHz,
    reproducibility: candidate.reproducibility,
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
    `- Baseline: ${result.baseline.path} (runs=${result.baseline.runCount}, p95 CV=${fmtNumber(result.baseline.reproducibility.p95Cv, 4)}, throughput CV=${fmtNumber(result.baseline.reproducibility.throughputCv, 4)})`,
    '',
    '| candidate | runs | overall | p95 ratio | throughput ratio | error rate(%) | error limit(%) | peak RSS ratio | cold start ratio | p95 CV | throughput CV |',
    '|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|',
  ];

  for (const candidate of result.candidates) {
    lines.push(
      `| ${candidate.name} | ${candidate.runCount} | ${candidate.overall.toUpperCase()} | ${fmtNumber(candidate.comparison.p95Ratio, 4)} | ${fmtNumber(candidate.comparison.throughputRatio, 4)} | ${fmtNumber(candidate.metrics.errorRate, 2)} | ${fmtNumber(candidate.comparison.errorRateLimit, 2)} | ${fmtNumber(candidate.comparison.peakRssRatio, 4)} | ${fmtNumber(candidate.comparison.coldStartRatio, 4)} | ${fmtNumber(candidate.reproducibility.p95Cv, 4)} | ${fmtNumber(candidate.reproducibility.throughputCv, 4)} |`,
    );
  }

  lines.push(
    '',
    '## Required checks',
    '- p95 ratio <= 0.85',
    '- throughput ratio >= 1.20',
    '- error rate <= max(0.5, baseline + 0.2pt)',
    '- peak RSS ratio <= 1.15',
    '- p95 CV <= 0.05 (when runCount >= 2)',
    '- throughput CV <= 0.05 (when runCount >= 2)',
    '',
    '## Reference check',
    '- cold start ratio <= 1.10',
    '',
  );
  return lines.join('\n');
}

function main() {
  const options = parseArgs(process.argv.slice(2));
  const baselineRuns = options.baselinePaths.map((baselinePath) => readBenchmarkReport(baselinePath));
  const baseline = aggregateBenchmarkRuns(baselineRuns);
  const candidates = options.candidates.map((candidate) => {
    const runs = candidate.paths.map((candidatePath) => readBenchmarkReport(candidatePath));
    const aggregatedCandidate = aggregateBenchmarkRuns(runs);
    return evaluateCandidate({ ...candidate, ...aggregatedCandidate }, baseline);
  });

  const result = {
    schemaVersion: 'bench-compare/v1',
    generatedAt: new Date().toISOString(),
    baseline: {
      path: baseline.path,
      paths: baseline.paths,
      runCount: baseline.runCount,
      metrics: baseline.metrics,
      throughputHz: baseline.throughputHz,
      taskCount: baseline.taskCount,
      reproducibility: baseline.reproducibility,
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
