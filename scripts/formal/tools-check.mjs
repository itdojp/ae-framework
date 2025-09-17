#!/usr/bin/env node
import { execSync } from 'node:child_process';

function has(cmd) {
  try { execSync(`bash -lc 'command -v ${cmd}'`, { stdio: 'ignore' }); return true; } catch { return false; }
}

function version(cmd, args = ['--version']) {
  try { return execSync(`bash -lc '${cmd} ${args.join(' ')}'`, { encoding: 'utf8' }).trim(); } catch { return 'n/a'; }
}
function shortVer(tool, raw) {
  if (!raw || raw === 'n/a') return 'n/a';
  try {
    const line = String(raw).split('\n')[0];
    // Heuristics per tool
    if (tool === 'z3') {
      // "Z3 version 4.12.4 - 64 bit"
      const m = /Z3 version\s+([\w\.-]+)/i.exec(line); return m ? m[1] : line;
    }
    if (tool === 'cvc5') {
      // "cvc5 1.0.8"
      const m = /cvc5\s+([\w\.-]+)/i.exec(line); return m ? m[1] : line;
    }
    if (tool === 'apalache-mc') {
      // "apalache-mc version x.y.z-..."
      const m = /version\s+([\w\.-]+)/i.exec(line); return m ? m[1] : line;
    }
    if (tool === 'java') {
      // "openjdk version \"21.0.2\" 2024-01-16"
      const m = /version\s+"([\w\.-]+)"/i.exec(line); return m ? m[1] : line;
    }
    return line;
  } catch { return raw; }
}

const report = [];

// Java (for TLC)
const hasJava = has('java');
report.push({ tool: 'java', present: hasJava, version: hasJava ? shortVer('java', version('java', ['-version'])) : 'n/a' });

// TLC via TLA_TOOLS_JAR (best-effort)
const tlaJar = process.env.TLA_TOOLS_JAR || '';
report.push({ tool: 'tla2tools.jar', present: !!tlaJar, path: tlaJar || 'unset (set TLA_TOOLS_JAR=/path/to/tla2tools.jar)' });

// Apalache
const hasApalache = has('apalache-mc');
report.push({ tool: 'apalache-mc', present: hasApalache, version: hasApalache ? shortVer('apalache-mc', version('apalache-mc', ['version'])) : 'n/a' });

// Z3
const hasZ3 = has('z3');
report.push({ tool: 'z3', present: hasZ3, version: hasZ3 ? shortVer('z3', version('z3', ['--version'])) : 'n/a' });

// cvc5
const hasCvc5 = has('cvc5');
report.push({ tool: 'cvc5', present: hasCvc5, version: hasCvc5 ? shortVer('cvc5', version('cvc5', ['--version'])) : 'n/a' });

console.log('Formal tools status');
for (const r of report) {
  const status = r.present ? '✅' : '❌';
  const extra = r.version ? ` (${r.version})` : (r.path ? ` (${r.path})` : '');
  console.log(`- ${status} ${r.tool}${extra}`);
}

// One-line digest (non-blocking)
try {
  const map = Object.fromEntries(report.map(r => [r.tool, r.present]));
  const tlc = !!(process.env.TLA_TOOLS_JAR || '').trim();
  const line = [
    `tlc=${tlc?'yes':'no'}`,
    `apalache=${map['apalache-mc']?'yes':'no'}`,
    `z3=${map['z3']?'yes':'no'}`,
    `cvc5=${map['cvc5']?'yes':'no'}`,
    `java=${report.find(r=>r.tool==='java')?.version||'n/a'}`
  ].join(' ');
  console.log(`Tools: ${line}`);
} catch {}

// Non-blocking: always exit 0
process.exit(0);
