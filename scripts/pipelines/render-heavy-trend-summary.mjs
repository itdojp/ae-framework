#!/usr/bin/env node

/**
 * Render a readable summary for the heavy test trend history.
 * - Scans history JSON snapshots (default: reports/heavy-test-trends-history)
 * - Produces Markdown describing recent runs (most-recent first)
 * - Writes Markdown to stdout, summary.md, and optionally GITHUB_STEP_SUMMARY
 */

import { readdir, readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, '..', '..');

async function main() {
  const options = parseArgs(process.argv);
  const historyDir = path.resolve(repoRoot, options.historyDir);

  const files = await listJsonFiles(historyDir);
  if (files.length === 0) {
    const message = `No heavy test trend snapshots found under ${path.relative(repoRoot, historyDir)}`;
    console.log(message);
    await writeSummary(options.outputPath, `${message}\n`);
    await appendStepSummary(message);
    return;
  }

  const limitedFiles = files.slice(-options.limit).reverse();
  const sections = [];
  for (const file of limitedFiles) {
    const absolute = path.join(historyDir, file);
    try {
      const payload = JSON.parse(await readFile(absolute, 'utf8'));
      sections.push(renderSnapshot(path.basename(file, '.json'), payload));
    } catch (error) {
      sections.push(`### ${file}\nFailed to parse snapshot: ${error instanceof Error ? error.message : String(error)}\n`);
    }
  }

  const summary = sections.join('\n');
  console.log(summary);
  await writeSummary(options.outputPath, `${summary}\n`);
  await appendStepSummary(summary);
}

function parseArgs(argv) {
  const defaults = {
    historyDir: 'reports/heavy-test-trends-history',
    limit: 5,
    outputPath: path.resolve(repoRoot, 'reports', 'heavy-test-trends-history', 'summary.md'),
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

function renderSnapshot(label, payload) {
  const lines = [];
  const generatedAt = payload.generatedAt ?? 'Unknown time';
  const context = payload.context ?? {};

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
  for (const entry of entries) {
    if (!entry || !entry.metrics) {
      continue;
    }
    rows.push(`  - **${entry.label}**: ${formatMetrics(entry.metrics)}`);
  }
  if (rows.length === 0) {
    lines.push('- Metrics: なし（baseline もしくは current が欠落）');
  } else {
    lines.push('- Metrics:');
    lines.push(...rows);
  }
  lines.push('');
  return lines.join('\n');
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

await main();
