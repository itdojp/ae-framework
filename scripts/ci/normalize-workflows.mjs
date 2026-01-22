#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';

const args = new Set(process.argv.slice(2));
const apply = args.has('--apply');
const list = args.has('--list');
const ruleArgs = new Set();
for (const arg of process.argv.slice(2)) {
  if (arg.startsWith('--rule=')) {
    const value = arg.slice('--rule='.length).trim();
    if (value) ruleArgs.add(value);
  }
}

const rulesPath = join(process.cwd(), 'scripts', 'ci', 'normalize-rules.json');
const rules = JSON.parse(readFileSync(rulesPath, 'utf8'));
const available = rules.rules || [];

if (list) {
  console.log('Available normalization rules:');
  for (const rule of available) {
    console.log(`- ${rule.name}: ${rule.description || ''}`.trim());
  }
  process.exit(0);
}

const selected = ruleArgs.size > 0
  ? available.filter((rule) => ruleArgs.has(rule.name))
  : available;

if (selected.length === 0) {
  console.error('[normalize-workflows] No matching rules selected.');
  process.exit(1);
}

const run = (rule, command, extraArgs = []) => {
  const parts = command.split(' ');
  const cmd = parts[0];
  const cmdArgs = parts.slice(1).concat(extraArgs);
  execFileSync(cmd, cmdArgs, { stdio: 'inherit' });
};

for (const rule of selected) {
  if (!rule.command) continue;
  const extra = [];
  if (apply && rule.applyFlag) {
    extra.push(rule.applyFlag);
  }
  if (apply && !rule.applyFlag) {
    console.log(`[normalize-workflows] Rule "${rule.name}" is audit-only; apply is ignored.`);
  }
  console.log(`[normalize-workflows] Running ${rule.name}...`);
  run(rule, rule.command, extra);
}
