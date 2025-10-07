#!/usr/bin/env node

import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const inputPath = resolve(process.argv[2] || 'artifacts/runtime-guard/runtime-guard-stats.json');
const outputPath = process.argv[3] ? resolve(process.argv[3]) : null;

if (!existsSync(inputPath)) {
  console.error(`Runtime guard stats not found at ${inputPath}`);
  process.exit(1);
}

let payload;
try {
  payload = JSON.parse(readFileSync(inputPath, 'utf8'));
} catch (error) {
  console.error(`Failed to parse runtime guard stats: ${error.message}`);
  process.exit(1);
}

// The payload may either wrap stats under a `stats` key or provide the stats object directly.
let stats;
if (payload && typeof payload === 'object' && payload.stats && typeof payload.stats === 'object') {
  stats = payload.stats;
} else if (payload && typeof payload === 'object' && payload.last24Hours && typeof payload.last24Hours === 'object') {
  stats = payload;
} else {
  console.error('Input file does not contain expected stats structure.');
  process.exit(1);
}

const buckets = stats.last24Hours?.hourlyBuckets;
if (!Array.isArray(buckets) || buckets.length === 0) {
  console.error('No hourly bucket information found in runtime guard stats.');
  process.exit(1);
}

const lines = [
  'hour,count',
  ...buckets.map((bucket) => `${bucket.hour},${bucket.count}`),
];

const csv = lines.join('\n');
if (outputPath) {
  writeFileSync(outputPath, csv, 'utf8');
} else {
  console.log(csv);
}
