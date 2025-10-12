#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { collectSurvivors, readMutationReport } from './list-survivors.mjs';

const DEFAULT_REPORT = path.resolve('reports/mutation/mutation.json');
const REPORT_HTML = path.resolve('reports/mutation/mutation.html');
const SUMMARY_JSON = path.resolve('reports/mutation/summary.json');

async function loadReport() {
  if (fs.existsSync(DEFAULT_REPORT)) {
    return readMutationReport(DEFAULT_REPORT);
  }
  if (!fs.existsSync(REPORT_HTML)) {
    throw new Error('mutation report not found: ' + DEFAULT_REPORT);
  }
  const html = fs.readFileSync(REPORT_HTML, 'utf8');
  const match = html.match(/app\.report\s*=\s*(\{[\s\S]*?\});/);
  if (!match) {
    throw new Error('unable to locate app.report JSON payload in mutation report');
  }
  return JSON.parse(match[1]);
}

function computeSummary(report) {
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
  const mutationScore = denominator === 0 ? 100 : (detected / denominator) * 100;

  return {
    totalMutants: total,
    killed: counters.Killed,
    survived: counters.Survived,
    timedOut: counters.Timeout,
    noCoverage: counters.NoCoverage,
    ignored: counters.Ignored,
    runtimeErrors: counters.RuntimeError,
    compileErrors: counters.CompileError,
    mutationScore: Number(mutationScore.toFixed(2)),
  };
}

function renderConsole(summary) {
  const rows = [
    ['Mutation score', `${summary.mutationScore}%`],
    ['Total mutants', summary.totalMutants],
    ['Killed', summary.killed],
    ['Survived', summary.survived],
    ['Timed out', summary.timedOut],
    ['Runtime errors', summary.runtimeErrors],
    ['Compile errors', summary.compileErrors],
    ['No coverage', summary.noCoverage],
    ['Ignored', summary.ignored],
  ];
  const width = Math.max(...rows.map(([label]) => label.length));
  for (const [label, value] of rows) {
    console.log(`${label.padEnd(width)} : ${value}`);
  }
}

function appendStepSummary(summary) {
  const summaryPath = process.env.GITHUB_STEP_SUMMARY;
  if (!summaryPath) {
    return;
  }
  const lines = [
    '### Mutation Quick Summary',
    '',
    `- Mutation score: **${summary.mutationScore}%**`,
    `- Total mutants: ${summary.totalMutants}`,
    `- Killed: ${summary.killed}`,
    `- Survived: ${summary.survived}`,
    `- Timed out: ${summary.timedOut}`,
    `- Runtime errors: ${summary.runtimeErrors}`,
    `- Compile errors: ${summary.compileErrors}`,
    `- No coverage: ${summary.noCoverage}`,
    `- Ignored: ${summary.ignored}`,
    '',
  ];
  fs.appendFileSync(summaryPath, lines.join('\n'));
}

function writeSummaryJson(summary) {
  fs.mkdirSync(path.dirname(SUMMARY_JSON), { recursive: true });
  fs.writeFileSync(SUMMARY_JSON, JSON.stringify(summary, null, 2));
}

async function main() {
  try {
    const report = await loadReport();
    const summary = computeSummary(report);
    writeSummaryJson(summary);
    renderConsole(summary);
    appendStepSummary(summary);
  } catch (error) {
    console.error('[mutation-report]', error.message);
    process.exitCode = 1;
  }
}

await main();
