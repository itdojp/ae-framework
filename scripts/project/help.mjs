#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, '..', '..');
const pkgPath = path.join(root, 'package.json');

const pkg = JSON.parse(fs.readFileSync(pkgPath, 'utf8'));
const scripts = pkg.scripts || {};

const groups = new Map();
for (const name of Object.keys(scripts).sort()) {
  const prefix = name.includes(':') ? name.split(':')[0] : 'core';
  if (!groups.has(prefix)) {
    groups.set(prefix, []);
  }
  groups.get(prefix).push(name);
}

const lines = [];
lines.push('ae-framework script groups (pnpm run <script>):');
lines.push('');

for (const [prefix, names] of [...groups.entries()].sort()) {
  const sample = names.slice(0, 5).join(', ');
  lines.push(`- ${prefix} (${names.length}): ${sample}`);
}

lines.push('');
lines.push('Tips:');
lines.push('- pnpm run <script>');
lines.push('- pnpm run | less');

console.log(lines.join('\n'));
