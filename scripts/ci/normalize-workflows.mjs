#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';

const rawArgs = process.argv.slice(2);
const args = new Set(rawArgs);
const apply = args.has('--apply');
const list = args.has('--list');
const ruleArgs = new Set();
for (const arg of rawArgs) {
  if (arg.startsWith('--rule=')) {
    const value = arg.slice('--rule='.length).trim();
    if (value) ruleArgs.add(value);
  }
}

const unknownArgs = rawArgs.filter(
  (arg) => arg.startsWith('-') && arg !== '--apply' && arg !== '--list' && !arg.startsWith('--rule=')
);
if (unknownArgs.length > 0) {
  console.warn(`[normalize-workflows] Warning: unrecognized argument(s): ${unknownArgs.join(', ')}`);
}

const rulesPath = join(process.cwd(), 'scripts', 'ci', 'normalize-rules.json');
let rules;
try {
  rules = JSON.parse(readFileSync(rulesPath, 'utf8'));
} catch (error) {
  console.error('[normalize-workflows] Failed to load or parse normalize-rules.json at:', rulesPath);
  console.error('[normalize-workflows] Error:', error && error.message ? error.message : error);
  process.exit(1);
}
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
if (ruleArgs.size > 0) {
  const invalid = [...ruleArgs].filter((name) => !available.some((rule) => rule.name === name));
  if (invalid.length > 0) {
    console.error(`[normalize-workflows] Unknown rule(s): ${invalid.join(', ')}`);
    console.error('[normalize-workflows] Run with --list to see available rules.');
    process.exit(1);
  }
}

if (selected.length === 0) {
  console.error('[normalize-workflows] No matching rules selected.');
  process.exit(1);
}

const splitCommand = (command) => {
  if (Array.isArray(command)) return command;
  if (typeof command !== 'string') return [];
  const tokens = command.match(/\"[^\"]+\"|'[^']+'|\\S+/g) || [];
  return tokens.map((token) => token.replace(/^['"]|['"]$/g, ''));
};

const run = (rule, command, extraArgs = []) => {
  const parts = splitCommand(command);
  const cmd = parts[0];
  const cmdArgs = parts.slice(1).concat(extraArgs);
  execFileSync(cmd, cmdArgs, { stdio: 'inherit' });
};

let hadFailures = false;
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
  try {
    run(rule, rule.command, extra);
  } catch (error) {
    hadFailures = true;
    console.error(
      `[normalize-workflows] Rule \"${rule.name}\" failed:`,
      error && error.message ? error.message : error
    );
  }
}

if (hadFailures) {
  process.exit(1);
}
