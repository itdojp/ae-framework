#!/usr/bin/env node
import { readFileSync } from 'node:fs';

const [,, summaryPath] = process.argv;
if (!summaryPath) {
  console.error('Usage: node scripts/verify/render-contracts-summary.mjs <contracts-exec.json>');
  process.exit(1);
}

let summary;
try {
  const raw = readFileSync(summaryPath, 'utf8');
  summary = JSON.parse(raw);
} catch (error) {
  console.error(`Failed to read runtime contracts summary at ${summaryPath}:`, error instanceof Error ? error.message : String(error));
  process.exit(1);
}

console.log('## Runtime Contracts Summary');
console.log();

if (!summary || typeof summary !== 'object') {
  console.log('_contracts-exec summary is empty or malformed._');
  process.exit(0);
}

const results = summary.results;
if (results && typeof results.error === 'string') {
  console.log('❌ Contract execution reported an error:');
  console.log();
  console.log('```');
  console.log(results.error);
  console.log('```');
  process.exit(0);
}

if (!results || typeof results !== 'object') {
  console.log('_No contract result details available._');
  process.exit(0);
}

const flags = [
  ['parseInOk', 'Request schema parse'],
  ['preOk', 'Pre-condition'],
  ['postOk', 'Post-condition'],
  ['parseOutOk', 'Response schema parse'],
];

console.log('| Check | Status |');
console.log('| --- | --- |');
for (const [key, label] of flags) {
  const status = results[key];
  if (typeof status === 'boolean') {
    console.log(`| ${label} | ${status ? '✅' : '❌'} |`);
  }
}

const violations = results.violations;
if (Array.isArray(violations) && violations.length > 0) {
  console.log();
  console.log('Detected violations:');
  for (const violation of violations) {
    if (violation && typeof violation === 'object') {
      const id = violation.id || 'unknown';
      const message = violation.message || violation.details || 'Violation detected';
      console.log(`- **${id}**: ${message}`);
    }
  }
}
