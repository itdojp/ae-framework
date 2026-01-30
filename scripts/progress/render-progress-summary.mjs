#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const readJson = (p) => {
  try {
    return JSON.parse(fs.readFileSync(p, 'utf8'));
  } catch {
    return undefined;
  }
};

const formatPercent = (value) => {
  if (typeof value !== 'number' || Number.isNaN(value)) return 'n/a';
  return `${Math.round(value)}%`;
};

const formatRatio = (value) => {
  if (typeof value !== 'number' || Number.isNaN(value)) return 'n/a';
  return `${Math.round(value * 1000) / 10}%`;
};

const formatDelta = (current, previous, unit = '%') => {
  if (typeof current !== 'number' || typeof previous !== 'number') return '';
  const delta = Math.round((current - previous) * 10) / 10;
  const sign = delta >= 0 ? '+' : '';
  return ` (Δ ${sign}${delta}${unit})`;
};

const summaryPath = process.env.PROGRESS_SUMMARY_PATH ?? path.join('artifacts', 'progress', 'summary.json');
const previousPath = process.env.PROGRESS_SUMMARY_PREVIOUS;
const outputPath = process.env.PROGRESS_SUMMARY_MD ?? path.join('artifacts', 'progress', 'PR_PROGRESS.md');

const summary = readJson(summaryPath);
if (!summary) {
  console.error(`progress summary not found: ${summaryPath}`);
  process.exit(1);
}

const previous = previousPath ? readJson(previousPath) : undefined;

const progress = summary.progress || null;
const quality = summary.quality || null;
const metrics = summary.metrics || null;
const traceability = summary.traceability || null;
const missing = Array.isArray(summary.missing) ? summary.missing : [];

const lines = ['## Progress Summary'];

if (progress) {
  const percent = formatPercent(progress.percent);
  const delta = formatDelta(progress.percent, previous?.progress?.percent);
  const currentPhase = progress.currentPhase ?? 'n/a';
  const completed = progress.phasesCompleted ?? 0;
  const total = progress.phasesTotal ?? 0;
  lines.push(`- Progress: ${percent}${delta} (phase=${currentPhase}, ${completed}/${total})`);
}

if (quality) {
  const score = typeof quality.overallScore === 'number' ? quality.overallScore : 'n/a';
  const scoreDelta = formatDelta(quality.overallScore, previous?.quality?.overallScore, '');
  const env = quality.environment ?? 'n/a';
  const passed = quality.passedGates ?? 0;
  const total = quality.totalGates ?? 0;
  const blockers = Array.isArray(quality.blockers) ? quality.blockers.length : 0;
  lines.push(`- Quality: ${env} score=${score}${scoreDelta} gates=${passed}/${total} blockers=${blockers}`);
}

if (metrics) {
  const tdd = formatPercent(metrics.tddCompliance);
  const tddDelta = formatDelta(metrics.tddCompliance, previous?.metrics?.tddCompliance);
  const coverage = formatPercent(metrics.overallCoverage);
  const coverageDelta = formatDelta(metrics.overallCoverage, previous?.metrics?.overallCoverage);
  const violations = metrics.totalViolations ?? 0;
  const violationsDelta = formatDelta(metrics.totalViolations, previous?.metrics?.totalViolations, '');
  lines.push(`- Metrics: TDD=${tdd}${tddDelta} coverage=${coverage}${coverageDelta} violations=${violations}${violationsDelta}`);
}

if (traceability) {
  const total = traceability.total ?? 0;
  const tests = formatRatio(traceability.coverage?.tests);
  const testsDelta = formatDelta(traceability.coverage?.tests, previous?.traceability?.coverage?.tests);
  const impl = formatRatio(traceability.coverage?.impl);
  const implDelta = formatDelta(traceability.coverage?.impl, previous?.traceability?.coverage?.impl);
  const formal = formatRatio(traceability.coverage?.formal);
  const formalDelta = formatDelta(traceability.coverage?.formal, previous?.traceability?.coverage?.formal);
  lines.push(`- Traceability: tests=${tests}${testsDelta} impl=${impl}${implDelta} formal=${formal}${formalDelta} (total=${total})`);
}

if (missing.length > 0) {
  lines.push(`- Missing: ${missing.join(', ')}`);
}

fs.mkdirSync(path.dirname(outputPath), { recursive: true });
fs.writeFileSync(outputPath, `${lines.join('\n')}\n`, 'utf8');
console.log(`✓ Wrote ${outputPath}`);
