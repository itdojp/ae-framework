#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const OUTPUT_MARKDOWN_PATH = 'artifacts/testing/repro-summary.md';
const OUTPUT_JSON_PATH = 'artifacts/testing/repro-summary.json';
const SUMMARY_SOURCES = [
  { name: 'property', paths: ['artifacts/properties/summary.json'] },
  { name: 'replay', paths: ['artifacts/domain/replay.summary.json', 'artifacts/replay/summary.json'] },
  { name: 'mbt', paths: ['artifacts/mbt/summary.json'] },
];

function readJsonIfExists(filePath) {
  if (!fs.existsSync(filePath)) {
    return null;
  }
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    return {
      _parseError: error instanceof Error ? error.message : String(error),
    };
  }
}

function ensureParentDir(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function toNumber(value, fallback = 0) {
  return Number.isFinite(Number(value)) ? Number(value) : fallback;
}

function normalizeStatus(summary) {
  if (!summary || typeof summary !== 'object') {
    return 'missing';
  }
  if (typeof summary.passed === 'boolean') {
    return summary.passed ? 'pass' : 'fail';
  }
  if (typeof summary.failed === 'number') {
    return summary.failed > 0 ? 'fail' : 'pass';
  }
  if (typeof summary.violations === 'number') {
    return summary.violations > 0 ? 'fail' : 'pass';
  }
  if (Array.isArray(summary.violatedInvariants)) {
    return summary.violatedInvariants.length > 0 ? 'fail' : 'pass';
  }
  return 'unknown';
}

function normalizeRuns(summary) {
  if (!summary || typeof summary !== 'object') {
    return 0;
  }
  return toNumber(summary.runs ?? summary.totalEvents ?? summary.scenarios?.length ?? 0, 0);
}

function normalizePassed(summary, runs) {
  if (!summary || typeof summary !== 'object') {
    return 0;
  }
  if (typeof summary.passed === 'boolean') {
    return summary.passed ? runs : 0;
  }
  if (typeof summary.passed === 'number') {
    return summary.passed;
  }
  return 0;
}

function normalizeFailed(summary, runs, passed) {
  if (!summary || typeof summary !== 'object') {
    return 0;
  }
  if (typeof summary.failed === 'number') {
    return summary.failed;
  }
  if (typeof summary.passed === 'boolean') {
    return summary.passed ? 0 : Math.max(1, runs === 0 ? 1 : runs);
  }
  if (typeof summary.violations === 'number') {
    return summary.violations > 0 ? Math.max(1, summary.violations) : 0;
  }
  if (Array.isArray(summary.violatedInvariants)) {
    return summary.violatedInvariants.length > 0 ? 1 : 0;
  }
  return Math.max(0, runs - passed);
}

function normalizeRecord(name, sourcePath, summary) {
  if (!summary || typeof summary !== 'object' || summary._parseError) {
    return {
      name,
      sourcePath,
      status: summary?._parseError ? 'invalid_json' : 'missing',
      traceId: null,
      seed: null,
      runs: 0,
      passed: 0,
      failed: 0,
      durationMs: 0,
      reproducibleCommand: null,
      counterexamplePath: null,
      parseError: summary?._parseError ?? null,
    };
  }
  const runs = normalizeRuns(summary);
  const passed = normalizePassed(summary, runs);
  const failed = normalizeFailed(summary, runs, passed);
  return {
    name,
    sourcePath,
    status: normalizeStatus(summary),
    traceId: summary.traceId ?? null,
    seed: summary.seed ?? null,
    runs,
    passed,
    failed,
    durationMs: toNumber(summary.durationMs, 0),
    reproducibleCommand: summary.reproducibleCommand ?? null,
    counterexamplePath: summary.counterexamplePath ?? null,
    parseError: null,
  };
}

function renderMarkdown(records) {
  const lines = [];
  lines.push('# Testing Harness Reproducibility');
  lines.push('');
  lines.push('| Harness | Status | Seed | Trace | Runs | Passed | Failed | Duration(ms) |');
  lines.push('| --- | --- | ---: | --- | ---: | ---: | ---: | ---: |');
  for (const record of records) {
    lines.push(
      `| ${record.name} | ${record.status} | ${record.seed ?? 'n/a'} | ${record.traceId ?? 'n/a'} | ${record.runs} | ${record.passed} | ${record.failed} | ${record.durationMs} |`
    );
  }
  lines.push('');
  lines.push('## Repro Commands');
  lines.push('');
  for (const record of records) {
    if (!record.reproducibleCommand) {
      lines.push(`- ${record.name}: n/a`);
      continue;
    }
    lines.push(`- ${record.name}: \`${record.reproducibleCommand}\``);
  }
  const counterexamples = records.filter((record) => record.counterexamplePath);
  if (counterexamples.length > 0) {
    lines.push('');
    lines.push('## Counterexamples');
    lines.push('');
    for (const record of counterexamples) {
      lines.push(`- ${record.name}: \`${record.counterexamplePath}\``);
    }
  }
  return `${lines.join('\n')}\n`;
}

function appendStepSummary(markdown) {
  const summaryPath = process.env.GITHUB_STEP_SUMMARY;
  if (!summaryPath) {
    return;
  }
  ensureParentDir(summaryPath);
  fs.appendFileSync(summaryPath, markdown);
}

function run() {
  const records = SUMMARY_SOURCES.map((entry) => {
    for (const candidatePath of entry.paths) {
      const loaded = readJsonIfExists(candidatePath);
      if (loaded !== null) {
        return normalizeRecord(entry.name, candidatePath, loaded);
      }
    }
    return normalizeRecord(entry.name, entry.paths[0], null);
  });

  const payload = {
    generatedAtUtc: new Date().toISOString(),
    records,
  };
  const markdown = renderMarkdown(records);

  ensureParentDir(OUTPUT_JSON_PATH);
  fs.writeFileSync(OUTPUT_JSON_PATH, `${JSON.stringify(payload, null, 2)}\n`);
  ensureParentDir(OUTPUT_MARKDOWN_PATH);
  fs.writeFileSync(OUTPUT_MARKDOWN_PATH, markdown);
  appendStepSummary(markdown);
}

try {
  run();
} catch (error) {
  const message = error instanceof Error ? error.stack ?? error.message : String(error);
  process.stderr.write(`[render-testing-repro-summary] ${message}\n`);
  process.exit(1);
}
