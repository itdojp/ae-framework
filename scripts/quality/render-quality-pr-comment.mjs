#!/usr/bin/env node
/**
 * @fileoverview
 * Render a markdown summary and JSON sidecar for the latest quality-gates report
 * so it can be posted as a PR comment with optional delta hints.
 *
 * Usage:
 *   node scripts/quality/render-quality-pr-comment.mjs
 *
 * Environment variables:
 * - QUALITY_REPORT_PATH: explicit path to a quality report JSON file.
 * - QUALITY_COMMENT_OUTPUT: markdown output path (default: artifacts/quality/PR_QUALITY.md).
 * - QUALITY_SUMMARY_OUTPUT: JSON summary output path (default: artifacts/quality/summary.json).
 * - QUALITY_PREVIOUS_SUMMARY: path to previous summary JSON for delta comparisons.
 *
 * Exit codes:
 * - 0: success
 * - 3: failed to write outputs
 */
import fs from 'node:fs';
import path from 'node:path';

const cwd = process.cwd();

const readJsonOptional = (p) => {
  try {
    return JSON.parse(fs.readFileSync(p, 'utf8'));
  } catch {
    return undefined;
  }
};

const findLatestReport = () => {
  const explicit = process.env.QUALITY_REPORT_PATH;
  if (explicit && fs.existsSync(explicit)) {
    return path.resolve(explicit);
  }

  const dir = path.join(cwd, 'reports', 'quality-gates');
  const preferred = [
    'quality-report-ci-latest.json',
    'quality-report-testing-latest.json',
    'quality-report-development-latest.json',
    'quality-report-production-latest.json',
  ];

  for (const filename of preferred) {
    const candidate = path.join(dir, filename);
    if (fs.existsSync(candidate)) {
      return candidate;
    }
  }

  if (!fs.existsSync(dir)) {
    return null;
  }

  const entries = fs
    .readdirSync(dir)
    .filter((file) => file.startsWith('quality-report-') && file.endsWith('.json'))
    .map((file) => path.join(dir, file));

  if (!entries.length) {
    return null;
  }

  entries.sort((a, b) => fs.statSync(b).mtimeMs - fs.statSync(a).mtimeMs);
  return entries[0] ?? null;
};

const outputMd = process.env.QUALITY_COMMENT_OUTPUT ?? path.join('artifacts', 'quality', 'PR_QUALITY.md');
const outputJson = process.env.QUALITY_SUMMARY_OUTPUT ?? path.join('artifacts', 'quality', 'summary.json');
const previousPath = process.env.QUALITY_PREVIOUS_SUMMARY;

const reportPath = findLatestReport();
const report = reportPath ? readJsonOptional(reportPath) : undefined;
const previous = previousPath ? readJsonOptional(previousPath) : undefined;

if (reportPath) {
  console.log(`Using quality report: ${path.relative(cwd, reportPath)}`);
} else {
  console.log('No quality report found; emitting N/A summary.');
}

if (reportPath && !report) {
  console.warn(`Failed to parse quality report: ${path.relative(cwd, reportPath)}`);
}

if (previousPath && !previous) {
  console.warn(`Failed to parse previous summary: ${previousPath}`);
}

const results = Array.isArray(report?.results) ? report.results : [];
const failedResults = results.filter((result) => !result.passed);
const failedGateKeys = Array.from(
  new Set(
    failedResults
      .map((result) => result.gateKey || result.gateName || 'unknown')
      .filter(Boolean)
  )
);
const blockers = Array.isArray(report?.summary?.blockers) ? report.summary.blockers : [];
const blockersCount = blockers.length;

const summary = {
  generatedAt: new Date().toISOString(),
  source: reportPath ? path.relative(cwd, reportPath) : null,
  environment: report?.environment ?? null,
  overallScore: typeof report?.overallScore === 'number' ? report.overallScore : null,
  totalGates: typeof report?.totalGates === 'number' ? report.totalGates : null,
  passedGates: typeof report?.passedGates === 'number' ? report.passedGates : null,
  failedGates: typeof report?.failedGates === 'number' ? report.failedGates : null,
  blockersCount,
  blockers,
  failedGateKeys,
  status: report
    ? blockersCount > 0
      ? 'FAIL'
      : (report?.failedGates ?? 0) > 0
        ? 'WARN'
        : 'PASS'
    : 'N/A',
};

const formatDelta = (current, previousValue, decimals = 0, unit = '') => {
  if (typeof current !== 'number' || typeof previousValue !== 'number') return '';
  const delta = Number((current - previousValue).toFixed(decimals));
  const sign = delta >= 0 ? '+' : '';
  return ` (Δ ${sign}${delta}${unit})`;
};

const formatScore = (value) => {
  if (typeof value !== 'number') return 'n/a';
  return Number.isInteger(value) ? `${value}` : value.toFixed(1);
};

const formatCount = (value) => {
  if (typeof value !== 'number') return 'n/a';
  return `${value}`;
};

const formatListWithMore = (items, limit) => {
  if (!items.length) return '';
  const shown = items.slice(0, limit).join(', ');
  const remaining = items.length - limit;
  return remaining > 0 ? `${shown}... (and ${remaining} more)` : shown;
};

const prevFailed = Array.isArray(previous?.failedGateKeys) ? previous.failedGateKeys : [];
const newFailures = failedGateKeys.filter((key) => !prevFailed.includes(key));
const resolvedFailures = prevFailed.filter((key) => !failedGateKeys.includes(key));

const lines = ['## Quality Gates'];

if (!report) {
  lines.push('- Status: N/A (quality report not found)');
  lines.push('- Failed: n/a');
  lines.push(`- Report: ${summary.source ?? 'n/a'}`);
} else {
  const env = summary.environment ?? 'n/a';
  const score = formatScore(summary.overallScore);
  const scoreDelta = formatDelta(summary.overallScore, previous?.overallScore, 1);
  const hasGateCounts = typeof summary.passedGates === 'number' && typeof summary.totalGates === 'number';
  const gatesDelta = hasGateCounts && typeof previous?.passedGates === 'number'
    ? formatDelta(summary.passedGates, previous.passedGates, 0)
    : '';
  const gates = hasGateCounts
    ? `${summary.passedGates}/${summary.totalGates}${gatesDelta}`
    : 'n/a';
  const blockersText = `${formatCount(blockersCount)}${formatDelta(blockersCount, previous?.blockersCount, 0)}`;
  lines.push(`- Status: ${summary.status} | env=${env} | score=${score}${scoreDelta} | gates=${gates} | blockers=${blockersText}`);

  const failedList = failedGateKeys.length ? formatListWithMore(failedGateKeys, 3) : 'none';
  const diffParts = [];
  if (newFailures.length) diffParts.push(`new: ${formatListWithMore(newFailures, 3)}`);
  if (resolvedFailures.length) diffParts.push(`resolved: ${formatListWithMore(resolvedFailures, 3)}`);
  const diffNote = diffParts.length ? ` (${diffParts.join('; ')})` : '';
  lines.push(`- Failed: ${failedList}${diffNote}`);
  lines.push(`- Report: ${summary.source ?? 'n/a'}`);
}

try {
  fs.mkdirSync(path.dirname(outputMd), { recursive: true });
  fs.mkdirSync(path.dirname(outputJson), { recursive: true });
  fs.writeFileSync(outputMd, `${lines.join('\n')}\n`, 'utf8');
  fs.writeFileSync(outputJson, JSON.stringify(summary, null, 2));
  console.log(`✓ Wrote ${outputMd}`);
  process.exitCode = 0;
} catch (error) {
  const message = error instanceof Error ? error.message : String(error);
  console.error('Failed to write quality PR comment outputs:', message);
  process.exitCode = 3;
}
