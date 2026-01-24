#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, '..', '..');
const mapPath = path.join(root, 'scripts', 'admin', 'script-alias-map.json');

const legacy = process.argv[2];
if (!legacy || legacy.startsWith('-')) {
  console.error('Usage: node scripts/admin/run-script-alias.mjs <legacy-script>');
  process.exit(3);
}

let aliasMap;
try {
  aliasMap = JSON.parse(readFileSync(mapPath, 'utf8'));
} catch (error) {
  const message = error instanceof Error ? error.message : String(error ?? 'unknown error');
  console.error(`[script-alias] failed to load alias map: ${message}`);
  process.exit(1);
}

const aliases = Array.isArray(aliasMap.aliases) ? aliasMap.aliases : [];
const alias = aliases.find((item) => item.legacy === legacy);
if (!alias) {
  console.error(`[script-alias] unknown legacy script: ${legacy}`);
  process.exit(2);
}

const policy = aliasMap.deprecation?.policy;
const removalTarget = aliasMap.deprecation?.removalTarget;
console.warn(`[script-alias] "${legacy}" is deprecated. Use: ${alias.target}`);
if (policy || removalTarget) {
  const details = [removalTarget, policy].filter(Boolean).join(' ');
  console.warn(`[script-alias] Removal target: ${details}`);
}

const splitArgs = (command) => {
  const parts = command.match(/(?:[^\\s\"']+|\"[^\"]*\"|'[^']*')+/g) || [];
  return parts.map((part) => part.replace(/^['"]|['"]$/g, ''));
};

const [command, ...args] = splitArgs(alias.target);
if (!command) {
  console.error(`[script-alias] invalid target command for ${legacy}`);
  process.exit(3);
}

const result = spawnSync(command, args, {
  stdio: 'inherit',
  env: process.env,
});
if (result.error) {
  console.error(
    `[script-alias] failed to spawn command: ${alias.target}: ${result.error.message ?? result.error}`
  );
  process.exit(result.error.code === 'ENOENT' ? 127 : 1);
}
process.exit(result.status ?? 1);
