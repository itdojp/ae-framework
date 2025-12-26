#!/usr/bin/env node
// Lightweight TLA+ checker: prefers Apalache if installed; otherwise tries TLC via TLA_TOOLS_JAR.
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

function commandExists(cmd) {
  const result = spawnSync(cmd, [], { stdio: 'ignore' });
  if (result.error && result.error.code === 'ENOENT') return false;
  return true;
}

function run(cmd, args) {
  const display = [cmd, ...args].join(' ');
  console.log(`$ ${display}`);
  const result = spawnSync(cmd, args, { stdio: 'inherit' });
  if (result.error) return 1;
  return result.status ?? 0;
}

const spec = process.argv[2] || 'spec/tla/DomainSpec.tla';
if (!fs.existsSync(spec)) {
  console.log(`Spec not found: ${spec} (skipping)`);
  process.exit(0);
}

if (commandExists('apalache-mc')) {
  run('apalache-mc', ['check', '--inv=Invariant', spec]);
  process.exit(0);
}

if (process.env.TLA_TOOLS_JAR) {
  const jar = path.resolve(process.env.TLA_TOOLS_JAR);
  if (!fs.existsSync(jar)) {
    console.log(`TLA tools jar not found: ${jar} (skipping)`);
    process.exit(0);
  }
  if (!commandExists('java')) {
    console.log('Java runtime not found (skipping). See docs/quality/formal-tools-setup.md');
    process.exit(0);
  }
  run('java', ['-cp', jar, 'tlc2.TLC', spec]);
  process.exit(0);
}

console.log('No Apalache or TLA_TOOLS_JAR set. Use tools:formal:check and see formal-tools-setup.md');
process.exit(0);
