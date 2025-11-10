#!/usr/bin/env node

/**
 * Render a readable summary for the heavy test trend history.
 * - Scans history JSON snapshots (default: reports/heavy-test-trends-history)
 * - Produces Markdown describing recent runs (most-recent first)
 * - Evaluates metrics against Warning / Critical thresholds
 * - Writes Markdown to stdout, summary.md, and optionally GITHUB_STEP_SUMMARY
 * - Emits a JSON summary (alerts + metadata) for downstream automation
 */

import { readdir, readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, '..', '..');

const SEVERITY_ORDER = { ok: 0, warning: 1, critical: 2 };

async function main() {
  const options = parseArgs(process.argv);
  const historyDir = path.resolve(repoRoot, options.historyDir);

  const files = await listJsonFiles(historyDir);
  if (files.length === 0) {
    const message = `No heavy test trend snapshots found under ${path.relative(repoRoot, historyDir)}`;
    console.log(message);
    await writeSummary(options.outputPath, `${message}\n`);
    await appendStepSummary(message);
    await writeJsonSummary(options.jsonOutput, {
      generatedAt: new Date().toISOString(),
      historyDir: path.relative(repoRoot, historyDir),
      limit: options.limit,
      snapshots: [],
      highestSeverity: 'ok',
    });
    return;
  }

  const limitedFiles = files.slice(-options.limit).reverse();
  const sections = [];
  const snapshots = [];

  for (const file of limitedFiles) {
    const absolute = path.join(historyDir, file);
    try {
      const payload = JSON.parse(await readFile(absolute, 'utf8'));
      const result = processSnapshot(file, payload, options.thresholds);
      sections.push(result.markdown);
      snapshots.push(result.summary);
    } catch (error) {
      sections.push(`### ${file}\nFailed to parse snapshot: ${error instanceof Error ? error.message : String(error)}\n`);
    }
  }

  const alertSummary = renderAlertSummary(snapshots);
  const combined = [alertSummary, ...sections].filter(Boolean).join('\n\n');

  console.log(combined);
  await writeSummary(options.outputPath, `${combined}\n`);
  await appendStepSummary(combined);
  await writeJsonSummary(options.jsonOutput, {
    generatedAt: new Date().toISOString(),
    historyDir: path.relative(repoRoot, historyDir),
    limit: options.limit,
    snapshots,
    highestSeverity: summarizeHighestSeverity(snapshots),
  });
}

function parseArgs(argv) {
  const defaults = {
    historyDir: 'reports/heavy-test-trends-history',
    limit: 5,
    outputPath: path.resolve(repoRoot, 'reports', 'heavy-test-trends-history', 'summary.md'),
    jsonOutput: path.resolve(repoRoot, 'reports', 'heavy-test-trends-history', 'summary.json'),
    thresholds: {
      warnMutationScore: 98,
      criticalMutationScore: 96,
      warnMutationDelta: -1.0,
      criticalMutationDelta: -2.5,
      warnPropertyFailed: 1,
      criticalPropertyFailed: 3,
      warnPropertyFailureRate: 0.1,
      warnMbtViolations: 1,
      criticalMbtViolations: 3,
    },
  };

  for (let i = 2; i < argv.length; i += 1) {
    const current = argv[i];
    if ((current === '--history-dir' || current === '-d') && argv[i + 1]) {
      defaults.historyDir = argv[++i];
    } else if ((current === '--limit' || current === '-n') && argv[i + 1]) {
      const parsed = Number.parseInt(argv[++i], 10);
      if (!Number.isNaN(parsed) && parsed > 0) {
        defaults.limit = parsed;
      }
    } else if ((current === '--output' || current === '-o') && argv[i + 1]) {
      defaults.outputPath = path.resolve(repoRoot, argv[++i]);
    } else if ((current === '--json-output' || current === '--json') && argv[i + 1]) {
      defaults.jsonOutput = path.resolve(repoRoot, argv[++i]);
    } else {
      const next = argv[i + 1];
      switch (current) {
        case '--warn-mutation-score':
          defaults.thresholds.warnMutationScore = parseFloat(next);
          i += 1;
          break;
        case '--critical-mutation-score':
          defaults.thresholds.criticalMutationScore = parseFloat(next);
          i += 1;
          break;
        case '--warn-mutation-delta':
          defaults.thresholds.warnMutationDelta = parseFloat(next);
          i += 1;
          break;
        case '--critical-mutation-delta':
          defaults.thresholds.criticalMutationDelta = parseFloat(next);
          i += 1;
          break;
        case '--warn-property-failed':
          defaults.thresholds.warnPropertyFailed = Number.parseInt(next, 10);
          i += 1;
          break;
        case '--critical-property-failed':
          defaults.thresholds.criticalPropertyFailed = Number.parseInt(next, 10);
          i += 1;
          break;
        case '--warn-property-failure-rate':
          defaults.thresholds.warnPropertyFailureRate = parseFloat(next);
          i += 1;
          break;
        case '--warn-mbt-violations':
          defaults.thresholds.warnMbtViolations = Number.parseInt(next, 10);
          i += 1;
          break;
        case '--critical-mbt-violations':
          defaults.thresholds.criticalMbtViolations = Number.parseInt(next, 10);
          i += 1;
          break;
        default:
          break;
      }
    }
  }

  return defaults;
}

async function listJsonFiles(dir) {
  try {
    const entries = await readdir(dir);
    return entries.filter(name => name.endsWith('.json')).sort();
  } catch {
    return [];
  }
}

function processSnapshot(filename, payload, thresholds) {
  const label = path.basename(filename, '.json');
  const generatedAt = payload.generatedAt ?? 'Unknown time';
  const context = payload.context ?? {};

  const lines = [];
  lines.push(`### ${label}`);
  lines.push(`- Generated: ${generatedAt}`);

  const contextParts = [];
  if (context.runId) contextParts.push(`runId=${context.runId}`);
  if (context.runNumber) contextParts.push(`runNumber=${context.runNumber}`);
  if (context.sha) contextParts.push(`sha=${String(context.sha).slice(0, 12)}`);
  if (context.ref) contextParts.push(`ref=${context.ref}`);
  if (contextParts.length > 0) {
    lines.push(`- Context: ${contextParts.join(', ')}`);
  }

  const entries = Array.isArray(payload.entries) ? payload.entries : [];
  const rows = [];
  const entrySummaries = [];
  let snapshotSeverity = 'ok';

  for (const entry of entries) {
    if (!entry || !entry.metrics) {
      continue;
    }
    const evaluation = evaluateEntry(entry.label ?? 'Unknown', entry.metrics, thresholds);
    snapshotSeverity = maxSeverity(snapshotSeverity, evaluation.severity);
    entrySummaries.push({
      label: entry.label ?? 'Unknown',
      severity: evaluation.severity,
      reasons: evaluation.reasons,
      metrics: entry.metrics,
    });

    const icon = severityIcon(evaluation.severity);
    const metricsText = formatMetrics(entry.metrics);
    const reasonText = evaluation.reasons.length > 0 ? ` — ${evaluation.reasons.join('; ')}` : '';
    rows.push(`  - ${icon} **${entry.label ?? 'Unknown'}**: ${metricsText}${reasonText}`);
  }

  if (rows.length === 0) {
    lines.push('- Metrics: なし（baseline もしくは current が欠落）');
  } else {
    lines.push('- Metrics:');
    lines.push(...rows);
  }
  lines.push('');

  return {
    markdown: lines.join('\n'),
    summary: {
      file: filename,
      label,
      generatedAt,
      context,
      severity: snapshotSeverity,
      entries: entrySummaries,
    },
  };
}

function evaluateEntry(label, metrics, thresholds) {
  let severity = 'ok';
  const reasons = [];

  const setSeverity = (nextSeverity, reason) => {
    if (SEVERITY_ORDER[nextSeverity] > SEVERITY_ORDER[severity]) {
      severity = nextSeverity;
    }
    if (reason) {
      reasons.push(reason);
    }
  };

  if (metrics.mutationScore) {
    const score = metrics.mutationScore.current;
    const delta = metrics.mutationScore.delta;
    if (isFiniteNumber(score)) {
      if (score < thresholds.criticalMutationScore) {
        setSeverity('critical', `mutationScore ${score} < ${thresholds.criticalMutationScore}`);
      } else if (score < thresholds.warnMutationScore) {
        setSeverity('warning', `mutationScore ${score} < ${thresholds.warnMutationScore}`);
      }
    }
    if (isFiniteNumber(delta)) {
      if (delta <= thresholds.criticalMutationDelta) {
        setSeverity('critical', `Δ ${delta} <= ${thresholds.criticalMutationDelta}`);
      } else if (delta <= thresholds.warnMutationDelta) {
        setSeverity('warning', `Δ ${delta} <= ${thresholds.warnMutationDelta}`);
      }
    }
  }

  if (metrics.failed || metrics.runs) {
    const failed = metrics.failed?.current;
    const runs = metrics.runs?.current;
    if (isFiniteNumber(failed)) {
      if (failed >= thresholds.criticalPropertyFailed) {
        setSeverity('critical', `failed ${failed} >= ${thresholds.criticalPropertyFailed}`);
      } else if (failed >= thresholds.warnPropertyFailed) {
        setSeverity('warning', `failed ${failed} >= ${thresholds.warnPropertyFailed}`);
      }
    }
    if (isFiniteNumber(failed) && isFiniteNumber(runs) && runs > 0) {
      const rate = failed / runs;
      if (rate >= thresholds.warnPropertyFailureRate) {
        setSeverity('warning', `failure rate ${(rate * 100).toFixed(1)}% >= ${(thresholds.warnPropertyFailureRate * 100).toFixed(0)}%`);
      }
    }
  }

  if (metrics.violations) {
    const violations = metrics.violations?.current;
    if (isFiniteNumber(violations)) {
      if (violations >= thresholds.criticalMbtViolations) {
        setSeverity('critical', `violations ${violations} >= ${thresholds.criticalMbtViolations}`);
      } else if (violations >= thresholds.warnMbtViolations) {
        setSeverity('warning', `violations ${violations} >= ${thresholds.warnMbtViolations}`);
      }
    }
  }

  return { severity, reasons };
}

function formatMetrics(metrics) {
  const parts = [];
  for (const [metricName, values] of Object.entries(metrics)) {
    if (!values) {
      continue;
    }
    const baseline = formatValue(values.baseline);
    const current = formatValue(values.current);
    const delta = formatDelta(values.delta);
    parts.push(`${metricName}=${current} (baseline ${baseline}, Δ ${delta})`);
  }
  return parts.join('; ');
}

function formatValue(value) {
  if (value === null || typeof value === 'undefined') {
    return '—';
  }
  if (typeof value === 'number' && Number.isFinite(value)) {
    return value.toString();
  }
  return String(value);
}

function formatDelta(delta) {
  if (delta === null || typeof delta === 'undefined') {
    return '—';
  }
  if (typeof delta === 'number') {
    const sign = delta > 0 ? '+' : '';
    return `${sign}${delta}`;
  }
  return String(delta);
}

function severityIcon(severity) {
  if (severity === 'critical') {
    return ':rotating_light:';
  }
  if (severity === 'warning') {
    return ':warning:';
  }
  return '';
}

function maxSeverity(a, b) {
  return SEVERITY_ORDER[a] >= SEVERITY_ORDER[b] ? a : b;
}

function summarizeHighestSeverity(snapshots) {
  let highest = 'ok';
  for (const snapshot of snapshots) {
    highest = maxSeverity(highest, snapshot.severity ?? 'ok');
    for (const entry of snapshot.entries ?? []) {
      highest = maxSeverity(highest, entry.severity ?? 'ok');
    }
  }
  return highest;
}

function renderAlertSummary(snapshots) {
  if (snapshots.length === 0) {
    return '';
  }
  const lines = ['### Alert Summary'];
  const issues = [];
  for (const snapshot of snapshots) {
    for (const entry of snapshot.entries ?? []) {
      if (entry.severity && entry.severity !== 'ok') {
        const icon = severityIcon(entry.severity);
        const reasons = entry.reasons.join('; ');
        lines.push(`- ${icon} ${snapshot.label} — ${entry.label}: ${reasons || 'threshold exceeded'}`);
        issues.push(true);
      }
    }
  }
  if (issues.length === 0) {
    lines.push('- ✅ All monitored metrics within thresholds.');
  }
  return lines.join('\n');
}

async function writeSummary(outputPath, content) {
  await mkdir(path.dirname(outputPath), { recursive: true });
  await writeFile(outputPath, content, 'utf8');
}

async function appendStepSummary(content) {
  const target = process.env.GITHUB_STEP_SUMMARY;
  if (!target) {
    return;
  }
  const header = '## Heavy Test Trend History';
  const formatted = content.trimStart().startsWith('###') ? content : `### Snapshot\n${content}`;
  await writeFile(target, `${header}\n\n${formatted}\n`, { flag: 'a' });
}

async function writeJsonSummary(outputPath, payload) {
  await mkdir(path.dirname(outputPath), { recursive: true });
  await writeFile(outputPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
}

function isFiniteNumber(value) {
  return typeof value === 'number' && Number.isFinite(value);
}

await main();
