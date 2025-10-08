#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { renderVerifyLiteSummary } from './lib/verify-lite-summary.mjs';

const summaryPath = process.argv[2] ?? 'verify-lite-run-summary.json';
const resolved = path.resolve(summaryPath);

if (!fs.existsSync(resolved)) {
  console.log(`Verify Lite run summary not found: ${summaryPath}`);
  process.exit(0);
}

let summary;
try {
  const raw = fs.readFileSync(resolved, 'utf8');
  summary = JSON.parse(raw);
} catch (error) {
  console.error(`Failed to read summary ${summaryPath}: ${error.message}`);
  process.exit(1);
}

const serverUrl = process.env.GITHUB_SERVER_URL ?? 'https://github.com';
const repository = process.env.GITHUB_REPOSITORY;
const runId = process.env.GITHUB_RUN_ID;
const artifactsUrl = repository && runId ? `${serverUrl}/${repository}/actions/runs/${runId}?check_suite_focus=true#artifacts` : null;

const output = renderVerifyLiteSummary(summary, { artifactsUrl });
console.log(output);
