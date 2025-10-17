#!/usr/bin/env node

import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const DEFAULT_REPORT_PATH = 'reports/consolidated-test-report.json';

const [, , inputPath = DEFAULT_REPORT_PATH] = process.argv;
const thisDir = path.dirname(fileURLToPath(import.meta.url));
const resolvedPath = path.resolve(thisDir, '..', '..', inputPath);

const outputLines = ['## Docker test suites'];

try {
  const reportRaw = fs.readFileSync(resolvedPath, 'utf8');
  const data = JSON.parse(reportRaw);
  const suites = data?.suites ?? {};
  const lines = Object.entries(suites).map(([name, info]) => {
    const status = info && typeof info === 'object' && 'status' in info ? info.status : 'unknown';
    return `- ${name}: ${status ?? 'unknown'}`;
  });
  outputLines.push(...(lines.length ? lines : ['- no suites reported']));
} catch (error) {
  const message = error instanceof Error ? error.message : String(error);
  outputLines.push(`- failed to summarize report: ${message}`);
}

console.log(outputLines.join('\n'));
