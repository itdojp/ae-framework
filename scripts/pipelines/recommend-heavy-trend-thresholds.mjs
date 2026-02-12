#!/usr/bin/env node

import { readdir, readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, '..', '..');

const DEFAULT_THRESHOLDS = {
  warnMutationScore: 98,
  criticalMutationScore: 96,
  warnMutationDelta: -1.0,
  criticalMutationDelta: -2.5,
  warnPropertyFailed: 1,
  criticalPropertyFailed: 3,
  warnPropertyFailureRate: 0.1,
  warnMbtViolations: 1,
  criticalMbtViolations: 3,
};

async function main() {
  const options = parseArgs(process.argv);
  const historyDir = path.resolve(repoRoot, options.historyDir);
  const historyDirLabel = formatDisplayPath(historyDir);
  const files = await listJsonFiles(historyDir);

  if (files.length === 0) {
    const message = `No heavy test trend snapshots found under ${historyDirLabel}`;
    console.log(message);
    await writeOutputs(options, message, {
      generatedAt: new Date().toISOString(),
      historyDir: historyDirLabel,
      snapshotCount: 0,
      minSnapshots: options.minSnapshots,
      status: 'no_data',
      recommendations: null,
    });
    return;
  }

  const aggregated = {
    mutationScore: [],
    mutationDelta: [],
    propertyFailed: [],
    propertyFailureRate: [],
    mbtViolations: [],
  };
  let parsedSnapshotCount = 0;

  for (const file of files) {
    const absolute = path.join(historyDir, file);
    try {
      const payload = JSON.parse(await readFile(absolute, 'utf8'));
      collectMetrics(payload, aggregated);
      parsedSnapshotCount += 1;
    } catch (error) {
      console.warn(`Failed to parse ${file}: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  const recommendation = buildRecommendation(aggregated, options, parsedSnapshotCount, historyDirLabel);
  const markdown = renderMarkdown(historyDirLabel, recommendation);
  console.log(markdown);
  await writeOutputs(options, markdown, recommendation);
}

function parseArgs(argv) {
  const options = {
    historyDir: 'reports/heavy-test-trends-history',
    markdownOutput: path.resolve(repoRoot, 'reports', 'heavy-test-trends-history', 'threshold-recommendation.md'),
    jsonOutput: path.resolve(repoRoot, 'reports', 'heavy-test-trends-history', 'threshold-recommendation.json'),
    minSnapshots: 14,
    warnLowQuantile: 0.1,
    criticalLowQuantile: 0.05,
    warnHighQuantile: 0.9,
    criticalHighQuantile: 0.95,
  };

  for (let i = 2; i < argv.length; i += 1) {
    const current = argv[i];
    if ((current === '--history-dir' || current === '-d') && argv[i + 1]) {
      options.historyDir = argv[++i];
    } else if ((current === '--markdown-output' || current === '--md') && argv[i + 1]) {
      options.markdownOutput = path.resolve(repoRoot, argv[++i]);
    } else if ((current === '--json-output' || current === '--json') && argv[i + 1]) {
      options.jsonOutput = path.resolve(repoRoot, argv[++i]);
    } else if (current === '--min-snapshots' && argv[i + 1]) {
      const parsed = Number.parseInt(argv[++i], 10);
      if (Number.isFinite(parsed) && parsed > 0) {
        options.minSnapshots = parsed;
      }
    } else if (current === '--warn-low-quantile' && argv[i + 1]) {
      options.warnLowQuantile = clampQuantile(argv[++i], options.warnLowQuantile);
    } else if (current === '--critical-low-quantile' && argv[i + 1]) {
      options.criticalLowQuantile = clampQuantile(argv[++i], options.criticalLowQuantile);
    } else if (current === '--warn-high-quantile' && argv[i + 1]) {
      options.warnHighQuantile = clampQuantile(argv[++i], options.warnHighQuantile);
    } else if (current === '--critical-high-quantile' && argv[i + 1]) {
      options.criticalHighQuantile = clampQuantile(argv[++i], options.criticalHighQuantile);
    }
  }

  return options;
}

function clampQuantile(value, fallback) {
  const parsed = Number.parseFloat(value);
  if (!Number.isFinite(parsed)) {
    return fallback;
  }
  return Math.min(0.99, Math.max(0.01, parsed));
}

async function listJsonFiles(dir) {
  try {
    const entries = await readdir(dir);
    return entries
      .filter(name => name.endsWith('.json') && !name.startsWith('summary') && !name.startsWith('threshold-recommendation'))
      .sort();
  } catch {
    return [];
  }
}

function collectMetrics(payload, aggregated) {
  const entries = Array.isArray(payload?.entries) ? payload.entries : [];
  for (const entry of entries) {
    const metrics = entry?.metrics ?? {};

    const mutationScoreCurrent = metrics.mutationScore?.current;
    if (isFiniteNumber(mutationScoreCurrent)) {
      aggregated.mutationScore.push(mutationScoreCurrent);
    }
    const mutationScoreDelta = metrics.mutationScore?.delta;
    if (isFiniteNumber(mutationScoreDelta)) {
      aggregated.mutationDelta.push(mutationScoreDelta);
    }

    const failedCurrent = metrics.failed?.current;
    const runsCurrent = metrics.runs?.current;
    if (isFiniteNumber(failedCurrent)) {
      aggregated.propertyFailed.push(failedCurrent);
    }
    if (isFiniteNumber(failedCurrent) && isFiniteNumber(runsCurrent) && runsCurrent > 0) {
      aggregated.propertyFailureRate.push(failedCurrent / runsCurrent);
    }

    const violationsCurrent = metrics.violations?.current;
    if (isFiniteNumber(violationsCurrent)) {
      aggregated.mbtViolations.push(violationsCurrent);
    }
  }
}

function buildRecommendation(aggregated, options, snapshotCount, historyDirLabel) {
  const enoughSnapshots = snapshotCount >= options.minSnapshots;

  const mutationScoreStats = summarizeSeries(aggregated.mutationScore);
  const mutationDeltaStats = summarizeSeries(aggregated.mutationDelta);
  const propertyFailedStats = summarizeSeries(aggregated.propertyFailed);
  const propertyFailureRateStats = summarizeSeries(aggregated.propertyFailureRate);
  const mbtViolationsStats = summarizeSeries(aggregated.mbtViolations);

  const suggestedWarnMutationScore = mutationScoreStats.count > 0
    ? roundDown(quantile(mutationScoreStats.sorted, options.warnLowQuantile), 1)
    : null;
  const suggestedCriticalMutationScore = mutationScoreStats.count > 0
    ? Math.min(
      roundDown(quantile(mutationScoreStats.sorted, options.criticalLowQuantile), 1),
      suggestedWarnMutationScore ?? Number.POSITIVE_INFINITY,
    )
    : null;

  const suggestedWarnMutationDelta = mutationDeltaStats.count > 0
    ? roundDown(quantile(mutationDeltaStats.sorted, options.warnLowQuantile), 1)
    : null;
  const suggestedCriticalMutationDelta = mutationDeltaStats.count > 0
    ? Math.min(
      roundDown(quantile(mutationDeltaStats.sorted, options.criticalLowQuantile), 1),
      suggestedWarnMutationDelta ?? Number.POSITIVE_INFINITY,
    )
    : null;

  const suggestedWarnPropertyFailedRaw = propertyFailedStats.count > 0
    ? Math.ceil(quantile(propertyFailedStats.sorted, options.warnHighQuantile))
    : null;
  const suggestedWarnPropertyFailed = suggestedWarnPropertyFailedRaw === null
    ? null
    : Math.max(1, suggestedWarnPropertyFailedRaw);
  const suggestedCriticalPropertyFailedRaw = propertyFailedStats.count > 0
    ? Math.ceil(quantile(propertyFailedStats.sorted, options.criticalHighQuantile))
    : null;
  const suggestedCriticalPropertyFailed = suggestedCriticalPropertyFailedRaw === null
    ? null
    : Math.max((suggestedWarnPropertyFailed ?? 1) + 1, suggestedCriticalPropertyFailedRaw);

  const suggestedWarnPropertyFailureRate = propertyFailureRateStats.count > 0
    ? Math.max(0.01, roundUp(quantile(propertyFailureRateStats.sorted, options.warnHighQuantile), 3))
    : null;

  const suggestedWarnMbtViolationsRaw = mbtViolationsStats.count > 0
    ? Math.ceil(quantile(mbtViolationsStats.sorted, options.warnHighQuantile))
    : null;
  const suggestedWarnMbtViolations = suggestedWarnMbtViolationsRaw === null
    ? null
    : Math.max(1, suggestedWarnMbtViolationsRaw);
  const suggestedCriticalMbtViolationsRaw = mbtViolationsStats.count > 0
    ? Math.ceil(quantile(mbtViolationsStats.sorted, options.criticalHighQuantile))
    : null;
  const suggestedCriticalMbtViolations = suggestedCriticalMbtViolationsRaw === null
    ? null
    : Math.max((suggestedWarnMbtViolations ?? 1) + 1, suggestedCriticalMbtViolationsRaw);

  return {
    generatedAt: new Date().toISOString(),
    historyDir: historyDirLabel,
    snapshotCount,
    minSnapshots: options.minSnapshots,
    status: enoughSnapshots ? 'ready' : 'insufficient_data',
    quantiles: {
      warnLow: options.warnLowQuantile,
      criticalLow: options.criticalLowQuantile,
      warnHigh: options.warnHighQuantile,
      criticalHigh: options.criticalHighQuantile,
    },
    currentThresholds: DEFAULT_THRESHOLDS,
    sampleCounts: {
      mutationScore: mutationScoreStats.count,
      mutationDelta: mutationDeltaStats.count,
      propertyFailed: propertyFailedStats.count,
      propertyFailureRate: propertyFailureRateStats.count,
      mbtViolations: mbtViolationsStats.count,
    },
    recommendations: {
      warnMutationScore: suggestedWarnMutationScore,
      criticalMutationScore: suggestedCriticalMutationScore,
      warnMutationDelta: suggestedWarnMutationDelta,
      criticalMutationDelta: suggestedCriticalMutationDelta,
      warnPropertyFailed: suggestedWarnPropertyFailed,
      criticalPropertyFailed: suggestedCriticalPropertyFailed,
      warnPropertyFailureRate: suggestedWarnPropertyFailureRate,
      warnMbtViolations: suggestedWarnMbtViolations,
      criticalMbtViolations: suggestedCriticalMbtViolations,
    },
  };
}

function formatDisplayPath(absolutePath) {
  const relative = path.relative(repoRoot, absolutePath);
  if (!relative.startsWith('..') && relative !== '') {
    return relative;
  }
  return absolutePath;
}

function summarizeSeries(values) {
  const sorted = values.filter(isFiniteNumber).sort((a, b) => a - b);
  return {
    count: sorted.length,
    sorted,
  };
}

function quantile(sorted, q) {
  if (!Array.isArray(sorted) || sorted.length === 0) {
    return Number.NaN;
  }
  if (sorted.length === 1) {
    return sorted[0];
  }
  const index = (sorted.length - 1) * q;
  const lower = Math.floor(index);
  const upper = Math.ceil(index);
  if (lower === upper) {
    return sorted[lower];
  }
  const weight = index - lower;
  return sorted[lower] + (sorted[upper] - sorted[lower]) * weight;
}

function roundDown(value, digits) {
  if (!Number.isFinite(value)) {
    return null;
  }
  const factor = 10 ** digits;
  return Math.floor(value * factor) / factor;
}

function roundUp(value, digits) {
  if (!Number.isFinite(value)) {
    return null;
  }
  const factor = 10 ** digits;
  return Math.ceil(value * factor) / factor;
}

function renderMarkdown(historyDir, recommendation) {
  const lines = [
    '# Heavy Test Threshold Recommendation',
    '',
    `- Generated at: ${recommendation.generatedAt}`,
    `- History dir: ${historyDir}`,
    `- Snapshots: ${recommendation.snapshotCount} (required >= ${recommendation.minSnapshots})`,
    `- Status: ${recommendation.status}`,
    '',
    '| Metric | Current Warning | Suggested Warning | Current Critical | Suggested Critical | Samples |',
    '| --- | --- | --- | --- | --- | --- |',
    row(
      'Mutation score (lower is worse)',
      recommendation.currentThresholds.warnMutationScore,
      recommendation.recommendations?.warnMutationScore,
      recommendation.currentThresholds.criticalMutationScore,
      recommendation.recommendations?.criticalMutationScore,
      recommendation.sampleCounts.mutationScore,
    ),
    row(
      'Mutation delta (more negative is worse)',
      recommendation.currentThresholds.warnMutationDelta,
      recommendation.recommendations?.warnMutationDelta,
      recommendation.currentThresholds.criticalMutationDelta,
      recommendation.recommendations?.criticalMutationDelta,
      recommendation.sampleCounts.mutationDelta,
    ),
    row(
      'Property failed count (higher is worse)',
      recommendation.currentThresholds.warnPropertyFailed,
      recommendation.recommendations?.warnPropertyFailed,
      recommendation.currentThresholds.criticalPropertyFailed,
      recommendation.recommendations?.criticalPropertyFailed,
      recommendation.sampleCounts.propertyFailed,
    ),
    row(
      'Property failure rate (higher is worse)',
      recommendation.currentThresholds.warnPropertyFailureRate,
      recommendation.recommendations?.warnPropertyFailureRate,
      'n/a',
      'n/a',
      recommendation.sampleCounts.propertyFailureRate,
    ),
    row(
      'MBT violations (higher is worse)',
      recommendation.currentThresholds.warnMbtViolations,
      recommendation.recommendations?.warnMbtViolations,
      recommendation.currentThresholds.criticalMbtViolations,
      recommendation.recommendations?.criticalMbtViolations,
      recommendation.sampleCounts.mbtViolations,
    ),
    '',
  ];

  if (recommendation.status !== 'ready') {
    lines.push(
      `> Data is not sufficient yet. Keep collecting schedule snapshots until at least ${recommendation.minSnapshots} samples are available.`,
      '',
    );
  }

  lines.push(
    '## Quantile settings',
    `- Low-side warning quantile: ${recommendation.quantiles.warnLow}`,
    `- Low-side critical quantile: ${recommendation.quantiles.criticalLow}`,
    `- High-side warning quantile: ${recommendation.quantiles.warnHigh}`,
    `- High-side critical quantile: ${recommendation.quantiles.criticalHigh}`,
    '',
  );

  return lines.join('\n');
}

function row(metric, currentWarn, suggestedWarn, currentCritical, suggestedCritical, samples) {
  return `| ${metric} | ${formatValue(currentWarn)} | ${formatValue(suggestedWarn)} | ${formatValue(currentCritical)} | ${formatValue(suggestedCritical)} | ${formatValue(samples)} |`;
}

function formatValue(value) {
  if (value === null || typeof value === 'undefined') {
    return '—';
  }
  if (typeof value === 'number') {
    return Number.isInteger(value) ? `${value}` : value.toString();
  }
  return String(value);
}

async function writeOutputs(options, markdown, payload) {
  if (options.markdownOutput) {
    await mkdir(path.dirname(options.markdownOutput), { recursive: true });
    await writeFile(options.markdownOutput, `${markdown.trimEnd()}\n`, 'utf8');
  }
  if (options.jsonOutput) {
    await mkdir(path.dirname(options.jsonOutput), { recursive: true });
    await writeFile(options.jsonOutput, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
  }
}

function isFiniteNumber(value) {
  return typeof value === 'number' && Number.isFinite(value);
}

await main();
