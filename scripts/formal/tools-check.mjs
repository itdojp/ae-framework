#!/usr/bin/env node
import { execSync } from 'node:child_process';

function has(cmd) {
  try { execSync(`bash -lc 'command -v ${cmd}'`, { stdio: 'ignore' }); return true; } catch { return false; }
}

function version(cmd, args = ['--version']) {
  try { return execSync(`bash -lc '${cmd} ${args.join(' ')}'`, { encoding: 'utf8' }).trim(); } catch { return 'n/a'; }
}

const report = [];

// Java (for TLC)
const hasJava = has('java');
report.push({ tool: 'java', present: hasJava, version: hasJava ? version('java', ['-version']).split('\n')[0] : 'n/a' });

// TLC via TLA_TOOLS_JAR (best-effort)
const tlaJar = process.env.TLA_TOOLS_JAR || '';
report.push({ tool: 'tla2tools.jar', present: !!tlaJar, path: tlaJar || 'unset (set TLA_TOOLS_JAR=/path/to/tla2tools.jar)' });

// Apalache
const hasApalache = has('apalache-mc');
report.push({ tool: 'apalache-mc', present: hasApalache, version: hasApalache ? version('apalache-mc', ['version']) : 'n/a' });

// Z3
const hasZ3 = has('z3');
report.push({ tool: 'z3', present: hasZ3, version: hasZ3 ? version('z3', ['--version']) : 'n/a' });

// cvc5
const hasCvc5 = has('cvc5');
report.push({ tool: 'cvc5', present: hasCvc5, version: hasCvc5 ? version('cvc5', ['--version']) : 'n/a' });

console.log('Formal tools status');
for (const r of report) {
  const status = r.present ? '✅' : '❌';
  const extra = r.version ? ` (${r.version})` : (r.path ? ` (${r.path})` : '');
  console.log(`- ${status} ${r.tool}${extra}`);
}

// Non-blocking: always exit 0
process.exit(0);

