#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import vm from 'node:vm';
import { readMutationReport } from './list-survivors.mjs';

const DEFAULT_REPORT = path.resolve('reports/mutation/mutation.json');
const HTML_REPORT_CANDIDATES = [
  path.resolve('reports/mutation/mutation.html'),
  path.resolve('reports/mutation/index.html'),
];
const SUMMARY_JSON = path.resolve('reports/mutation/summary.json');
const VM_TIMEOUT_MS =
  Number.parseInt(process.env.MUTATION_REPORT_VM_TIMEOUT ?? '2000', 10) || 2000;

async function loadReport() {
  if (fs.existsSync(DEFAULT_REPORT)) {
    return { report: await readMutationReport(DEFAULT_REPORT), source: DEFAULT_REPORT };
  }
  const htmlReport = HTML_REPORT_CANDIDATES.find((candidate) =>
    fs.existsSync(candidate),
  );
  if (!htmlReport) {
    throw new Error(
      'mutation report not found: ' +
        [DEFAULT_REPORT, ...HTML_REPORT_CANDIDATES].join(', '),
    );
  }
  const html = fs.readFileSync(htmlReport, 'utf8');
  const match = html.match(/app\.report\s*=\s*(\{[\s\S]*?\});/);
  if (!match) {
    throw new Error('unable to locate app.report JSON payload in mutation report');
  }
  const payload = match[1];
  try {
    return { report: JSON.parse(payload), source: htmlReport };
  } catch (jsonError) {
    try {
      const script = new vm.Script(`(${payload})`);
      const reportObject = script.runInNewContext({}, { timeout: VM_TIMEOUT_MS });
      if (!reportObject || typeof reportObject !== 'object') {
        throw new Error('app.report payload missing');
      }
      return { report: reportObject, source: htmlReport };
    } catch (vmError) {
      const summary = deriveSummaryFromSerializedReport(payload);
      if (!summary) {
        throw new Error('failed to parse mutation report: ' + (vmError.message ?? vmError));
      }
      console.warn(
        '[mutation-report] fell back to text summary parsing:',
        vmError.message ?? vmError,
      );
      return { summary, source: htmlReport };
    }
  }
}


function deriveSummaryFromSerializedReport(serialized) {
  if (typeof serialized !== 'string' || serialized.length === 0) {
    return null;
  }
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
  for (const status of Object.keys(counters)) {
    const pattern = '"status":"' + status + '"';
    let count = 0;
    let index = -1;
    while ((index = serialized.indexOf(pattern, index + 1)) !== -1) {
      count += 1;
    }
    counters[status] = count;
  }
  const total = Object.values(counters).reduce((sum, value) => sum + value, 0);
  if (total === 0) {
    return null;
  }
  const detected =
    counters.Killed +
    counters.Timeout +
    counters.RuntimeError +
    counters.CompileError;
  const denominator = Math.max(total - counters.Ignored - counters.NoCoverage, 0);
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
    const loaded = await loadReport();
    const summary = loaded.summary ?? computeSummary(loaded.report ?? {});
    if (!summary) {
      throw new Error('unable to derive mutation summary');
    }
    writeSummaryJson(summary);
    renderConsole(summary);
    appendStepSummary(summary);
  } catch (error) {
    console.error('[mutation-report]', error.message);
    process.exitCode = 1;
  }
}

await main();
