#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

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

const { timestamp, flags = {}, steps = {}, artifacts = {} } = summary;

const yesNo = (value) => (value ? '✅' : '❌');
const formatStatus = (status) => {
  if (!status) return 'n/a';
  const normalized = String(status).toLowerCase();
  if (normalized === 'success') return '✅ success';
  if (normalized === 'failure') return '❌ failure';
  if (normalized === 'skipped') return '⏭️ skipped';
  if (normalized === 'pending') return '… pending';
  return normalized;
};

const flagLines = [
  `- install flags: \`${flags.install ?? ''}\``,
  `- no frozen lockfile: ${yesNo(flags.noFrozen)}`,
  `- keep lint log: ${yesNo(flags.keepLintLog)}`,
  `- enforce lint: ${yesNo(flags.enforceLint)}`,
  `- run mutation: ${yesNo(flags.runMutation)}`,
];

const stepEntries = Object.entries(steps);
const orderedKeys = [
  'install',
  'specCompilerBuild',
  'typeCheck',
  'lint',
  'build',
  'bddLint',
  'mutationQuick',
];
const seen = new Set();
const orderedSteps = [];
for (const key of orderedKeys) {
  if (steps[key]) {
    orderedSteps.push([key, steps[key]]);
    seen.add(key);
  }
}
for (const [key, value] of stepEntries) {
  if (!seen.has(key)) {
    orderedSteps.push([key, value]);
  }
}

const titleCase = (name) =>
  name
    .replace(/([a-z0-9])([A-Z])/g, '$1 $2')
    .replace(/[-_]/g, ' ')
    .replace(/\b\w/g, (ch) => ch.toUpperCase());

const tableLines = [
  '| Step | Status | Notes |',
  '| --- | --- | --- |',
];
for (const [key, value] of orderedSteps) {
  const status = formatStatus(value?.status);
  const notes = value?.notes ? String(value.notes).replace(/\n/g, '<br>') : '';
  tableLines.push(`| ${titleCase(key)} | ${status} | ${notes} |`);
}

const artifactLines = [];
if (Object.keys(artifacts).length > 0) {
  artifactLines.push('\nArtifacts:');
  for (const [key, value] of Object.entries(artifacts)) {
    artifactLines.push(`- ${key}: ${value ?? 'n/a'}`);
  }
}

const output = [
  timestamp ? `Timestamp: ${timestamp}` : 'Timestamp: n/a',
  ...flagLines,
  '',
  ...tableLines,
  '',
  ...artifactLines,
];

console.log(output.join('\n'));
