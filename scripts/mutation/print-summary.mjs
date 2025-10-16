#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';

const DEFAULT_REPORT_PATH = 'reports/mutation/mutation.json';

async function loadMutationReport(inputPath) {
  const target = resolve(process.cwd(), inputPath ?? DEFAULT_REPORT_PATH);
  const raw = await readFile(target, 'utf8');
  return JSON.parse(raw);
}

function collectMetrics(report) {
  const files = Object.values(report.files ?? {});
  const metrics = {
    detected: 0,
    undetected: 0,
    survived: 0,
    noCoverage: 0,
    timeout: 0,
    compileErrors: 0,
    runtimeErrors: 0,
  };

  for (const fileEntry of files) {
    for (const mutant of fileEntry.mutants ?? []) {
      switch (mutant.status) {
        case 'Killed':
          metrics.detected += 1;
          break;
        case 'Survived':
          metrics.undetected += 1;
          metrics.survived += 1;
          break;
        case 'Timeout':
          metrics.detected += 1;
          metrics.timeout += 1;
          break;
        case 'NoCoverage':
          metrics.undetected += 1;
          metrics.noCoverage += 1;
          break;
        case 'RuntimeError':
          metrics.detected += 1;
          metrics.runtimeErrors += 1;
          break;
        case 'CompileError':
          metrics.detected += 1;
          metrics.compileErrors += 1;
          break;
        default:
          break;
      }
    }
  }

  metrics.total = metrics.detected + metrics.undetected;
  metrics.score =
    metrics.total === 0 ? 0 : (metrics.detected / metrics.total) * 100;

  return metrics;
}

async function main() {
  try {
    const report = await loadMutationReport(process.argv[2]);
    const metrics = collectMetrics(report);

    const outputs = [
      ['mutation-score', Math.round(metrics.score * 100) / 100],
      ['detected', metrics.detected],
      ['undetected', metrics.undetected],
      ['survived', metrics.survived],
      ['no-coverage', metrics.noCoverage],
      ['timeout', metrics.timeout],
      ['compile-errors', metrics.compileErrors],
      ['runtime-errors', metrics.runtimeErrors],
      ['report-path', 'reports/mutation'],
    ];

    for (const [key, value] of outputs) {
      console.log(`${key}=${value}`);
    }
  } catch (error) {
    console.error(
      'Failed to read mutation report:',
      error instanceof Error ? error.message : error
    );
    process.exit(1);
  }
}

main();
