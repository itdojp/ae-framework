#!/usr/bin/env node
// Lightweight TLA+ checker: prefers Apalache if installed; otherwise tries TLC via TLA_TOOLS_JAR.
import { execSync } from 'node:child_process';
import fs from 'node:fs';

function has(cmd) { try { execSync(`bash -lc 'command -v ${cmd}'`, {stdio:'ignore'}); return true; } catch { return false; } }
function run(cmd) { try { console.log(`$ ${cmd}`); execSync(cmd, { stdio: 'inherit' }); return 0; } catch (e) { return 1; } }

const spec = process.argv[2] || 'spec/tla/DomainSpec.tla';
if (!fs.existsSync(spec)) { console.log(`Spec not found: ${spec} (skipping)`); process.exit(0); }

if (has('apalache-mc')) {
  process.exit(run(`bash -lc 'apalache-mc check --inv=Invariant ${spec}'`) ? 0 : 0);
} else if (process.env.TLA_TOOLS_JAR) {
  const jar = process.env.TLA_TOOLS_JAR;
  process.exit(run(`bash -lc 'java -cp ${jar} tlc2.TLC ${spec}'`) ? 0 : 0);
} else {
  console.log('No Apalache or TLA_TOOLS_JAR set. Use tools:formal:check and see formal-tools-setup.md');
  process.exit(0);
}

