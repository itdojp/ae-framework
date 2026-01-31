#!/usr/bin/env node
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
  const gates = summary.passedGates !== null && summary.totalGates !== null
    ? `${summary.passedGates}/${summary.totalGates}${formatDelta(summary.passedGates, previous?.passedGates, 0)}`
    : 'n/a';
  const blockersText = `${formatCount(blockersCount)}${formatDelta(blockersCount, previous?.blockersCount, 0)}`;
  lines.push(`- Status: ${summary.status} | env=${env} | score=${score}${scoreDelta} | gates=${gates} | blockers=${blockersText}`);

  const failedList = failedGateKeys.length ? failedGateKeys.slice(0, 3).join(', ') : 'none';
  const diffParts = [];
  if (newFailures.length) diffParts.push(`new: ${newFailures.slice(0, 3).join(', ')}`);
  if (resolvedFailures.length) diffParts.push(`resolved: ${resolvedFailures.slice(0, 3).join(', ')}`);
  const diffNote = diffParts.length ? ` (${diffParts.join('; ')})` : '';
  lines.push(`- Failed: ${failedList}${diffNote}`);
  lines.push(`- Report: ${summary.source ?? 'n/a'}`);
}

fs.mkdirSync(path.dirname(outputMd), { recursive: true });
fs.mkdirSync(path.dirname(outputJson), { recursive: true });
fs.writeFileSync(outputMd, `${lines.join('\n')}\n`, 'utf8');
fs.writeFileSync(outputJson, JSON.stringify(summary));
console.log(`✓ Wrote ${outputMd}`);
