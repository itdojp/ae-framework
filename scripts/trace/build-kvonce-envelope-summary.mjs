#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const outputPath = process.argv[2] ?? 'artifacts/kvonce-trace-summary.json';
const baseDir = path.join('hermetic-reports', 'trace');
const cases = [
  { key: 'otlp', label: 'OTLP payload', dir: path.join(baseDir, 'otlp') },
  { key: 'ndjson', label: 'NDJSON sample', dir: path.join(baseDir, 'ndjson') }
];

const readJsonSafe = (file) => {
  try {
    return JSON.parse(fs.readFileSync(file, 'utf8'));
  } catch (error) {
    return null;
  }
};

const metadata = readJsonSafe(path.join(baseDir, 'kvonce-payload-metadata.json')) ?? {};
const casesSummary = [];

for (const item of cases) {
  const reportPath = path.join(item.dir, 'kvonce-validation.json');
  const projectionPath = path.join(item.dir, 'kvonce-projection.json');
  const validation = readJsonSafe(reportPath);
  const projection = readJsonSafe(projectionPath);
  if (!validation) {
    casesSummary.push({
      format: item.key,
      status: 'missing',
      issues: [],
      note: 'validation file missing'
    });
    continue;
  }
  const issues = Array.isArray(validation.issues) ? validation.issues : [];
  const trimmedIssues = issues.slice(0, 10).map((issue) => ({
    type: issue.type ?? 'unknown',
    key: issue.key ?? 'unknown',
    message: issue.message ?? ''
  }));
  casesSummary.push({
    format: item.key,
    valid: Boolean(validation.valid),
    issueCount: issues.length,
    issues: trimmedIssues,
    projectionStats: projection?.stats ?? undefined
  });
}

const summary = {
  schemaVersion: '1.0.0',
  generatedAt: new Date().toISOString(),
  payloadMetadata: {
    sourceType: metadata.sourceType ?? null,
    sourceDetail: metadata.sourceDetail ?? null,
    sha256: metadata.sha256 ?? null,
    sizeBytes: metadata.sizeBytes ?? null
  },
  cases: casesSummary
};

const destDir = path.dirname(outputPath);
if (!fs.existsSync(destDir)) {
  fs.mkdirSync(destDir, { recursive: true });
}

fs.writeFileSync(outputPath, JSON.stringify(summary, null, 2));
console.log(`[trace] wrote kvonce summary to ${outputPath}`);
