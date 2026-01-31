#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const DEFAULT_REQUIRED = [
  'artifacts/verify-lite/verify-lite-run-summary.json',
  'artifacts/report-envelope.json'
];

const args = new Set(process.argv.slice(2));
const strict = args.has('--strict') || process.env.REQUIRED_ARTIFACTS_STRICT === '1';
const requiredEnv = process.env.REQUIRED_ARTIFACTS;
const requiredList = requiredEnv
  ? requiredEnv.split(',').map((v) => v.trim()).filter(Boolean)
  : DEFAULT_REQUIRED;

if (requiredList.length === 0) {
  console.log('[required-artifacts] no required artifacts configured; skipping');
  process.exit(0);
}

const missing = [];
const invalidJson = [];
const ok = [];

for (const relPath of requiredList) {
  const resolved = path.resolve(relPath);
  if (!fs.existsSync(resolved)) {
    missing.push(relPath);
    continue;
  }
  if (resolved.endsWith('.json')) {
    try {
      JSON.parse(fs.readFileSync(resolved, 'utf8'));
    } catch (error) {
      invalidJson.push(relPath);
      continue;
    }
  }
  ok.push(relPath);
}

const summary = [
  `[required-artifacts] ok=${ok.length} missing=${missing.length} invalid_json=${invalidJson.length}`,
  ok.length > 0 ? `  ok: ${ok.join(', ')}` : null,
  missing.length > 0 ? `  missing: ${missing.join(', ')}` : null,
  invalidJson.length > 0 ? `  invalid_json: ${invalidJson.join(', ')}` : null,
].filter(Boolean);

console.log(summary.join('\n'));

if (strict && (missing.length > 0 || invalidJson.length > 0)) {
  console.error('[required-artifacts] strict mode: missing or invalid artifacts detected');
  process.exit(1);
}

process.exit(0);
