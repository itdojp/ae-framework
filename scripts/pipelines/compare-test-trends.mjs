#!/usr/bin/env node

import { readFile, appendFile, access, constants, mkdir, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { readMutationReport } from '../mutation/list-survivors.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, '..', '..');

const CACHE_ROOT = path.join(repoRoot, '.cache', 'test-results');
const BASELINE_ROOT = path.join(repoRoot, '.cache', 'test-results-baseline');

const TARGETS = [
  {
    label: 'Mutation quick',
    currentDir: path.join(repoRoot, 'reports', 'mutation'),
    baselineDir: path.join(BASELINE_ROOT, 'reports', 'mutation'),
    async collectMetrics(dir) {
      const reportPath = path.join(dir, 'mutation.json');
      if (!(await exists(reportPath))) {
        return null;
      }
      const report = await readMutationReport(reportPath);
      const files = Object.values(report.files ?? {});
      const counters = {
        Killed: 0,
        Survived: 0,
        Timeout: 0,
        NoCoverage: 0,
        Ignored: 0,
        RuntimeError: 0,
        CompileError: 0,
        Skipped: 0,
      };
      let total = 0;
      for (const file of files) {
        for (const mutant of file.mutants ?? []) {
          total += 1;
          if (mutant.status in counters) {
            counters[mutant.status] += 1;
          }
        }
      }
      const detected =
        counters.Killed +
        counters.Timeout +
        counters.RuntimeError +
        counters.CompileError;
      const denominator = Math.max(
        total - counters.Ignored - counters.NoCoverage,
        0,
      );
      const mutationScore =
        denominator === 0 ? 100 : (detected / denominator) * 100;
      return {
        totalMutants: total,
        killed: counters.Killed,
        survived: counters.Survived,
        timedOut: counters.Timeout,
        noCoverage: counters.NoCoverage,
        ignored: counters.Ignored,
        mutationScore: Number(mutationScore.toFixed(2)),
      };
    },
  },
  {
    label: 'MBT harness',
    currentDir: path.join(repoRoot, 'artifacts', 'mbt'),
    baselineDir: path.join(BASELINE_ROOT, 'artifacts', 'mbt'),
    async collectMetrics(dir) {
      const summaryPath = path.join(dir, 'summary.json');
      if (!(await exists(summaryPath))) {
        return null;
      }
      const summary = JSON.parse(await readFile(summaryPath, 'utf8'));
      return {
        seed: summary.seed ?? null,
        runs: summary.runs ?? null,
        depth: summary.depth ?? null,
        violations: summary.violations ?? null,
      };
    },
  },
  {
    label: 'Property harness',
    currentDir: path.join(repoRoot, 'artifacts', 'properties'),
    baselineDir: path.join(BASELINE_ROOT, 'artifacts', 'properties'),
    async collectMetrics(dir) {
      const summaryPath = path.join(dir, 'summary.json');
      if (!(await exists(summaryPath))) {
        return null;
      }
      const summary = JSON.parse(await readFile(summaryPath, 'utf8'));
      return {
        traceId: summary.traceId ?? summary.trace ?? null,
        runs: summary.runs ?? null,
        passed: summary.passed ?? null,
        failed: summary.failed ?? null,
      };
    },
  },
];

async function exists(targetPath) {
  try {
    await access(targetPath, constants.F_OK);
    return true;
  } catch {
    return false;
  }
}

function diffMetrics(baseline, current) {
  if (!current) {
    return null;
  }
  if (!baseline) {
    // No baseline => treat everything as new data
    return Object.fromEntries(
      Object.entries(current).map(([key, value]) => [
        key,
        {
          baseline: null,
          current: value ?? null,
          delta: null,
        },
      ]),
    );
  }
  const keys = new Set([
    ...Object.keys(baseline ?? {}),
    ...Object.keys(current ?? {}),
  ]);
  const result = {};
  for (const key of keys) {
    const baseValue = baseline?.[key] ?? null;
    const currentValue = current?.[key] ?? null;
    let delta = null;
    if (
      typeof baseValue === 'number' &&
      typeof currentValue === 'number' &&
      Number.isFinite(baseValue) &&
      Number.isFinite(currentValue)
    ) {
      delta = Number((currentValue - baseValue).toFixed(2));
    } else if (
      typeof baseValue === 'string' &&
      typeof currentValue === 'string' &&
      baseValue !== currentValue
    ) {
      delta = currentValue;
    }
    result[key] = {
      baseline: baseValue,
      current: currentValue,
      delta,
    };
  }
  return result;
}

function renderMarkdown(comparisons) {
  const lines = [];
  for (const entry of comparisons) {
    lines.push(`### ${entry.label}`);
    if (!entry.metrics) {
      lines.push(
        entry.reason ??
          'No comparison available (missing baseline or current results).',
      );
      lines.push('');
      continue;
    }
    lines.push('| Metric | Baseline | Current | Δ |');
    lines.push('| --- | --- | --- | --- |');
    for (const [metric, values] of Object.entries(entry.metrics)) {
      const { baseline, current, delta } = values;
      lines.push(
        `| ${metric} | ${formatValue(baseline)} | ${formatValue(current)} | ${formatDelta(delta)} |`,
      );
    }
    lines.push('');
  }
  return lines.join('\n');
}

function formatValue(value) {
  if (value === null || typeof value === 'undefined') {
    return '—';
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
  return delta;
}

async function main() {
  const args = parseArgs(process.argv);
  const comparisons = [];
  for (const target of TARGETS) {
    const baseline = await target.collectMetrics(target.baselineDir);
    const current = await target.collectMetrics(target.currentDir);
    if (!current) {
      comparisons.push({
        label: target.label,
        reason: `Current results missing (${target.currentDir})`,
        metrics: null,
      });
      continue;
    }
    if (!baseline) {
      comparisons.push({
        label: target.label,
        reason: 'Baseline results missing (first run or cache miss)',
        metrics: diffMetrics(null, current),
      });
      continue;
    }
    comparisons.push({
      label: target.label,
      metrics: diffMetrics(baseline, current),
    });
  }

  const markdown = renderMarkdown(comparisons);
  console.log(markdown);
  if (process.env.GITHUB_STEP_SUMMARY) {
    await appendFile(
      process.env.GITHUB_STEP_SUMMARY,
      `### Heavy Test Trend Comparison\n\n${markdown}\n`,
    );
  }

  const jsonReport = {
    generatedAt: new Date().toISOString(),
    context: collectGithubContext(),
    entries: comparisons,
  };
  const outputPath = path.resolve(repoRoot, args.jsonOutput);
  await mkdir(path.dirname(outputPath), { recursive: true });
  await writeFile(outputPath, JSON.stringify(jsonReport, null, 2), 'utf8');
  console.log(`Trend comparison JSON written to ${path.relative(repoRoot, outputPath)}`);
}

function collectGithubContext() {
  const context = {
    eventName: process.env.GITHUB_EVENT_NAME ?? null,
    workflow: process.env.GITHUB_WORKFLOW ?? null,
    job: process.env.GITHUB_JOB ?? null,
    runId: process.env.GITHUB_RUN_ID ?? null,
    runNumber: process.env.GITHUB_RUN_NUMBER ?? null,
    runAttempt: process.env.GITHUB_RUN_ATTEMPT ?? null,
    repository: process.env.GITHUB_REPOSITORY ?? null,
    sha: process.env.GITHUB_SHA ?? null,
    ref: process.env.GITHUB_REF ?? null,
    actor: process.env.GITHUB_ACTOR ?? null,
  };
  if (Object.values(context).every(value => value === null)) {
    return null;
  }
  return context;
}

function parseArgs(argv) {
  const defaults = {
    jsonOutput: 'reports/heavy-test-trends.json',
  };
  for (let i = 2; i < argv.length; i += 1) {
    const current = argv[i];
    if ((current === '--json-output' || current === '-o') && argv[i + 1]) {
      defaults.jsonOutput = argv[i + 1];
      i += 1;
    }
  }
  return defaults;
}

await main();
