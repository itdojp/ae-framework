#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { appendSection } from '../ci/step-summary.mjs';

const baseDir = path.join('hermetic-reports', 'trace');
const cases = [
  { key: 'otlp', label: 'OTLP payload', dir: process.env.KVONCE_TRACE_OTLP_DIR ?? path.join(baseDir, 'otlp') },
  { key: 'ndjson', label: 'NDJSON sample', dir: process.env.KVONCE_TRACE_NDJSON_DIR ?? path.join(baseDir, 'ndjson') },
];

const outputPath = process.env.GITHUB_OUTPUT;
const outputs = {};
const lines = [];
let exitCode = 0;
const MAX_INLINE_ISSUES = 5;

const metadataPath = path.join(baseDir, 'kvonce-payload-metadata.json');
if (fs.existsSync(metadataPath)) {
  try {
    const metadata = JSON.parse(fs.readFileSync(metadataPath, 'utf8'));
    lines.push(`- payload source: ${metadata.sourceType ?? 'unknown'} (${metadata.sourceDetail ?? 'n/a'})`);
    lines.push(`- sha256: ${metadata.sha256 ?? 'unknown'}`);
    lines.push(`- size: ${metadata.sizeBytes ?? 'n/a'} bytes`);
  } catch (error) {
    lines.push('- payload metadata: ⚠️ failed to parse');
  }
}

for (const item of cases) {
  const reportPath = path.join(item.dir, 'kvonce-validation.json');
  if (!fs.existsSync(reportPath)) {
    lines.push(`- ${item.label}: ⚠️ validation file missing`);
    outputs[`valid_${item.key}`] = 'missing';
    outputs[`issues_${item.key}`] = 'N/A';
    continue;
  }
  try {
    const report = JSON.parse(fs.readFileSync(reportPath, 'utf8'));
    const issues = Array.isArray(report.issues) ? report.issues : [];
    const status = report.valid ? '✅ valid' : '❌ invalid';
    lines.push(`- ${item.label}: ${status} (issues: ${issues.length})`);
    if (issues.length > 0) {
      for (const issue of issues.slice(0, MAX_INLINE_ISSUES)) {
        const type = issue.type ?? 'unknown';
        const key = issue.key ?? 'unknown';
        const message = issue.message ?? '';
        const rendered = `  - [${type}] ${key}: ${message}`;
        lines.push(rendered.trimEnd());
      }
      if (issues.length > MAX_INLINE_ISSUES) {
        lines.push(`  - … (${issues.length - MAX_INLINE_ISSUES} more)`);
      }
    }
    outputs[`valid_${item.key}`] = report.valid ? 'true' : 'false';
    outputs[`issues_${item.key}`] = issues.length.toString();
    if (!report.valid) {
      exitCode = 1;
    }
  } catch (error) {
    lines.push(`- ${item.label}: ⚠️ failed to read validation (${error.message})`);
    outputs[`valid_${item.key}`] = 'error';
    outputs[`issues_${item.key}`] = 'N/A';
    exitCode = 1;
  }
}

appendSection('KvOnce Trace Validation', lines);

if (outputPath) {
  for (const [key, value] of Object.entries(outputs)) {
    fs.appendFileSync(outputPath, `${key}=${value}\n`);
  }
}

process.exitCode = exitCode;
