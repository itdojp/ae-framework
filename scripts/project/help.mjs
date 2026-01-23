#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, '..', '..');
const pkgPath = path.join(root, 'package.json');

let pkg;
try {
  const pkgContent = fs.readFileSync(pkgPath, 'utf8');
  pkg = JSON.parse(pkgContent);
} catch (err) {
  const message = err instanceof Error ? err.message : String(err);
  console.error(`Failed to read or parse package.json at "${pkgPath}": ${message}`);
  process.exit(1);
}
const scripts = pkg.scripts || {};

const groups = new Map();
for (const name of Object.keys(scripts).sort()) {
  const prefix = name.includes(':') ? name.split(':')[0] : '(root)';
  if (!groups.has(prefix)) {
    groups.set(prefix, []);
  }
  groups.get(prefix).push(name);
}

const lines = [];
const projectName = pkg.name || 'project';
lines.push(`${projectName} script groups (pnpm run <script>):`);
lines.push('');

for (const [prefix, names] of [...groups.entries()].sort()) {
  const shownCount = Math.min(5, names.length);
  const sample = names.slice(0, shownCount).join(', ');
  const suffix =
    names.length > shownCount ? ` ... (showing ${shownCount} of ${names.length})` : '';
  lines.push(`- ${prefix} (${names.length}): ${sample}${suffix}`);
}

const runnerCandidates = [
  { category: 'test', entry: 'scripts/test/run.mjs' },
  { category: 'quality', entry: 'scripts/quality/run.mjs' },
  { category: 'verify', entry: 'scripts/verify/run.mjs' },
  { category: 'flake', entry: 'scripts/flake/run.mjs' },
  { category: 'security', entry: 'scripts/security/run.mjs' },
];
const availableRunners = runnerCandidates.filter((runner) =>
  fs.existsSync(path.join(root, runner.entry))
);

if (availableRunners.length > 0) {
  lines.push('');
  lines.push('Consolidated runners (Phase 1):');
  for (const runner of availableRunners) {
    lines.push(`- ${runner.category}: node ${runner.entry} --list`);
  }
}

lines.push('');
lines.push('Tips:');
lines.push('- pnpm run <script>');
lines.push('- pnpm run | less');

console.log(lines.join('\n'));
