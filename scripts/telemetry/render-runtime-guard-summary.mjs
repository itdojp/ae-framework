#!/usr/bin/env node

import { existsSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const inputPath = resolve(process.argv[2] || 'artifacts/runtime-guard/runtime-guard-stats.json');

if (!existsSync(inputPath)) {
  console.log('Runtime guard stats not found. Skipping summary render.');
  process.exit(0);
}

let payload;
try {
  payload = JSON.parse(readFileSync(inputPath, 'utf8'));
} catch (error) {
  console.error(`Failed to parse runtime guard stats at ${inputPath}:`, error instanceof Error ? error.message : String(error));
  process.exit(1);
}

const stats = payload.stats ?? payload;
if (!stats || typeof stats !== 'object') {
  console.log('Runtime guard stats payload is empty.');
  process.exit(0);
}

const lines = [];
lines.push('## Runtime Guard Statistics');
if (payload.generatedAt) {
  lines.push(`_Generated at ${payload.generatedAt}_`);
}
lines.push('');
lines.push(`- Total violations: ${stats.total ?? 0}`);
lines.push(`- Last 24h: ${stats.last24Hours?.total ?? 0}`);

if (stats.byType) {
  lines.push('');
  lines.push('### Violations by Type');
  lines.push('| Type | Total | Last 24h |');
  lines.push('| --- | ---: | ---: |');
  for (const [type, total] of Object.entries(stats.byType)) {
    const last24 = stats.last24Hours?.byType?.[type] ?? 0;
    lines.push(`| ${type} | ${total} | ${last24} |`);
  }
}

if (stats.last24Hours?.hourlyBuckets?.length) {
  lines.push('');
  lines.push('### Last 24h Timeline');
  const buckets = stats.last24Hours.hourlyBuckets.slice(-12);
  for (const bucket of buckets) {
    lines.push(`- ${bucket.hour}: ${bucket.count}`);
  }
}

if (stats.byEndpoint && Object.keys(stats.byEndpoint).length > 0) {
  lines.push('');
  lines.push('### Top Endpoints');
  lines.push('| Endpoint | Violations |');
  lines.push('| --- | ---: |');
  const topEndpoints = Object.entries(stats.byEndpoint).slice(0, 5);
  for (const [endpoint, count] of topEndpoints) {
    lines.push(`| ${endpoint} | ${count} |`);
  }
}

if (Array.isArray(stats.recent) && stats.recent.length > 0) {
  lines.push('');
  lines.push('### Recent Violations');
  const recent = stats.recent.slice(0, 5);
  for (const violation of recent) {
    const ts = violation.timestamp || 'unknown time';
    const endpoint = violation.endpoint ?? 'unknown';
    lines.push(`- ${ts} — ${violation.type} (${violation.severity}) @ ${endpoint}`);
  }
}

console.log(lines.join('\n'));
