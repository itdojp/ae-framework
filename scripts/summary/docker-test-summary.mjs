#!/usr/bin/env node

import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const DEFAULT_REPORT_PATH = 'reports/consolidated-test-report.json';
export const DOCKER_TEST_HEADER = '## Docker test suites';

export function resolveReportPath(reportPath = DEFAULT_REPORT_PATH) {
  const thisDir = path.dirname(fileURLToPath(import.meta.url));
  return path.resolve(thisDir, '..', '..', reportPath);
}

export function summarizeSuites(suites) {
  const entries = Object.entries(suites ?? {});
  if (entries.length === 0) {
    return ['- no suites reported'];
  }
  return entries.map(([name, info]) => {
    const status =
      info && typeof info === 'object' && 'status' in info ? info.status : undefined;
    return `- ${name}: ${status ?? 'unknown'}`;
  });
}

export function summarizeReport({
  reportPath = DEFAULT_REPORT_PATH,
  readFileSyncImpl = readFileSync,
} = {}) {
  const lines = [DOCKER_TEST_HEADER];
  try {
    const resolvedPath = resolveReportPath(reportPath);
    const raw = readFileSyncImpl(resolvedPath, 'utf8');
    const data = JSON.parse(raw);
    lines.push(...summarizeSuites(data?.suites));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    lines.push(`- failed to summarize report: ${message}`);
  }
  return lines.join('\n');
}

export function main(argv = process.argv, log = console.log) {
  const [, , inputPath] = argv;
  const summary = summarizeReport({ reportPath: inputPath });
  log(summary);
}

const isInvokedDirectly = () => {
  try {
    return path.resolve(process.argv[1] ?? '') === fileURLToPath(import.meta.url);
  } catch {
    return false;
  }
};

if (isInvokedDirectly()) {
  main();
}
