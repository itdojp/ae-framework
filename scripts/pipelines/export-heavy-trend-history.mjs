#!/usr/bin/env node

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
    console.log(`No history files found in ${path.relative(repoRoot, historyDir)}`);
    return;
  }

  const rows = [];
  for (const file of files) {
    const absolute = path.join(historyDir, file);
    try {
      const payload = JSON.parse(await readFile(absolute, 'utf8'));
      rows.push(...flattenSnapshot(path.basename(file, '.json'), payload));
    } catch (error) {
      console.warn(`Failed to parse ${file}:`, error);
    }
  }

  await writeCsv(options.csvOutput, rows);
  if (options.markdownOutput) {
    await writeMarkdown(options.markdownOutput, rows, options.limitMarkdown);
  }
  if (options.statsOutput) {
    await writeStats(options.statsOutput, rows);
  }
}

function parseArgs(argv) {
  const defaults = {
    historyDir: 'reports/heavy-test-trends-history',
    csvOutput: path.resolve(repoRoot, 'reports', 'heavy-test-trends-history', 'history.csv'),
    markdownOutput: path.resolve(repoRoot, 'reports', 'heavy-test-trends-history', 'history.md'),
    limitMarkdown: 10,
    statsOutput: path.resolve(repoRoot, 'reports', 'heavy-test-trends-history', 'stats.json'),
  };

  for (let i = 2; i < argv.length; i += 1) {
    const current = argv[i];
    if ((current === '--history-dir' || current === '-d') && argv[i + 1]) {
      defaults.historyDir = argv[++i];
    } else if ((current === '--csv-output' || current === '--csv') && argv[i + 1]) {
      defaults.csvOutput = path.resolve(repoRoot, argv[++i]);
    } else if ((current === '--markdown-output' || current === '--md') && argv[i + 1]) {
      defaults.markdownOutput = path.resolve(repoRoot, argv[++i]);
    } else if (current === '--no-markdown') {
      defaults.markdownOutput = null;
    } else if (current === '--markdown-limit' && argv[i + 1]) {
      const parsed = Number.parseInt(argv[++i], 10);
      if (!Number.isNaN(parsed) && parsed > 0) {
        defaults.limitMarkdown = parsed;
      }
    } else if ((current === '--stats-output' || current === '--stats') && argv[i + 1]) {
      defaults.statsOutput = path.resolve(repoRoot, argv[++i]);
    } else if (current === '--no-stats') {
      defaults.statsOutput = null;
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

function flattenSnapshot(snapshotLabel, payload) {
  const rows = [];
  const entries = Array.isArray(payload.entries) ? payload.entries : [];
  for (const entry of entries) {
    const label = entry.label ?? 'Unknown';
    const metrics = entry.metrics ?? {};
    for (const [metricName, values] of Object.entries(metrics)) {
      if (!values) continue;
      rows.push({
        snapshot: snapshotLabel,
        label,
        metric: metricName,
        baseline: sanitizeNumber(values.baseline),
        current: sanitizeNumber(values.current),
        delta: sanitizeNumber(values.delta),
      });
    }
  }
  return rows;
}

function sanitizeNumber(value) {
  if (typeof value === 'number' && Number.isFinite(value)) {
    return value;
  }
  return '';
}

async function writeCsv(outputPath, rows) {
  await mkdir(path.dirname(outputPath), { recursive: true });
  const headers = ['snapshot', 'label', 'metric', 'baseline', 'current', 'delta'];
  const lines = [headers.join(',')];
  for (const row of rows) {
    lines.push(headers.map(key => row[key] === undefined ? '' : row[key]).join(','));
  }
  await writeFile(outputPath, `${lines.join('\n')}\n`, 'utf8');
  console.log(`CSV written to ${path.relative(repoRoot, outputPath)}`);
}

async function writeMarkdown(outputPath, rows, limit) {
  await mkdir(path.dirname(outputPath), { recursive: true });
  const limited = rows.slice(-limit);
  const lines = ['| Snapshot | Label | Metric | Baseline | Current | Δ |', '| --- | --- | --- | --- | --- | --- |'];
  for (const row of limited) {
    lines.push(`| ${row.snapshot} | ${row.label} | ${row.metric} | ${formatValue(row.baseline)} | ${formatValue(row.current)} | ${formatValue(row.delta)} |`);
  }
  await writeFile(outputPath, `${lines.join('\n')}\n`, 'utf8');
  console.log(`Markdown preview written to ${path.relative(repoRoot, outputPath)}`);
}

function formatValue(value) {
  if (value === '' || value === null || typeof value === 'undefined') {
    return '—';
  }
  return value;
}

async function writeStats(outputPath, rows) {
  const grouped = {};
  for (const row of rows) {
    if (row.current === '' || row.current === null || typeof row.current === 'undefined') {
      continue;
    }
    const key = `${row.label}::${row.metric}`;
    if (!grouped[key]) {
      grouped[key] = [];
    }
    grouped[key].push(Number(row.current));
  }
  const stats = Object.entries(grouped).map(([key, values]) => {
    const [label, metric] = key.split('::');
    return {
      label,
      metric,
      count: values.length,
      mean: Number(mean(values).toFixed(3)),
      stddev: values.length > 1 ? Number(stddev(values).toFixed(3)) : 0,
      min: Number(Math.min(...values).toFixed(3)),
      max: Number(Math.max(...values).toFixed(3)),
    };
  });
  await mkdir(path.dirname(outputPath), { recursive: true });
  await writeFile(outputPath, `${JSON.stringify({ generatedAt: new Date().toISOString(), stats }, null, 2)}\n`, 'utf8');
  console.log(`Stats written to ${path.relative(repoRoot, outputPath)}`);
}

function mean(values) {
  if (values.length === 0) return 0;
  return values.reduce((acc, cur) => acc + cur, 0) / values.length;
}

function stddev(values) {
  if (values.length <= 1) return 0;
  const avg = mean(values);
  const variance = values.reduce((acc, cur) => acc + (cur - avg) ** 2, 0) / (values.length - 1);
  return Math.sqrt(variance);
}

await main();
