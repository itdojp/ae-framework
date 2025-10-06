#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const summaryPath = process.argv[2] ?? 'verify-lite-lint-summary.json';
const baselinePath = process.argv[3] ?? 'config/verify-lite-lint-baseline.json';
const resolvedSummary = path.resolve(summaryPath);
const resolvedBaseline = path.resolve(baselinePath);

if (!fs.existsSync(resolvedSummary)) {
  console.error(`[verify-lite] lint summary not found at ${resolvedSummary}`);
  process.exit(1);
}

if (!fs.existsSync(resolvedBaseline)) {
  console.error(`[verify-lite] lint baseline not found at ${resolvedBaseline}`);
  process.exit(1);
}

const parseJson = (file) => {
  try {
    return JSON.parse(fs.readFileSync(file, 'utf8'));
  } catch (error) {
    console.error(`[verify-lite] failed to parse ${file}:`, error);
    process.exit(1);
  }
};

const summary = parseJson(resolvedSummary);
const baseline = parseJson(resolvedBaseline);
const enforce = process.env.VERIFY_LITE_LINT_ENFORCE === '1';
const summaryRules = new Map();
for (const entry of summary.rules ?? []) {
  summaryRules.set(entry.rule, entry.count);
}

const messages = [];
let violations = 0;

if (typeof summary.total === 'number' && typeof baseline.total === 'number') {
  const delta = summary.total - baseline.total;
  const status = delta <= 0 ? '✅' : '❌';
  const formattedDelta = delta >= 0 ? `, +${delta}` : `, ${delta}`;
  messages.push(`${status} Total issues: ${summary.total} (baseline ${baseline.total}${formattedDelta})`);
  if (delta > 0) violations += delta;
}

const baselineRules = baseline.rules ?? {};
for (const [rule, limit] of Object.entries(baselineRules)) {
  const actual = summaryRules.get(rule) ?? 0;
  const delta = actual - limit;
  const status = delta <= 0 ? '✅' : '❌';
  const formattedRuleDelta = delta >= 0 ? `, +${delta}` : `, ${delta}`;
  messages.push(`${status} ${rule}: ${actual} (baseline ${limit}${formattedRuleDelta})`);
  if (delta > 0) {
    violations += delta;
  }
}

if (Object.keys(baselineRules).length === 0) {
  messages.push('ℹ️ No per-rule baselines defined.');
}

const enforcementNote = enforce ? 'ENFORCED' : 'WARN-ONLY';
messages.unshift(`### Verify Lite Lint Baseline (${enforcementNote})`);

console.log(messages.join('\n'));

if (enforce && violations > 0) {
  process.exit(1);
}
