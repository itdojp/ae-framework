#!/usr/bin/env node
import { execSync } from 'node:child_process';

function has(cmd) {
  try { execSync(`bash -lc 'command -v ${cmd}'`, { stdio: 'ignore' }); return true; } catch { return false; }
}

function version(cmd, args = ['--version']) {
  try { return execSync(`bash -lc '${cmd} ${args.join(' ')} 2>&1'`, { encoding: 'utf8' }).trim(); } catch { return 'n/a'; }
}
function supportsSummaryJson() {
  try {
    const out = execSync("bash -lc 'cspx typecheck --help 2>&1'", { encoding: 'utf8' });
    return String(out).includes('--summary-json');
  } catch (e) {
    const out = `${e?.stdout ? String(e.stdout) : ''}${e?.stderr ? String(e.stderr) : ''}`;
    return out.includes('--summary-json');
  }
}
function shortVer(tool, raw) {
  if (!raw || raw === 'n/a') return 'n/a';
  try {
    const line = String(raw).split('\n')[0];
    // Heuristics per tool
    if (tool === 'spin') {
      // "Spin Version 6.5.2 -- 2 May 2019"
      const m = /Spin Version\s+([\w\.-]+)/i.exec(line); return m ? m[1] : line;
    }
    if (tool === 'gcc') {
      // "gcc (Ubuntu 11.4.0-1ubuntu1~22.04) 11.4.0"
      const m = /\b(\d+\.\d+(?:\.\d+)?)\b/.exec(line); return m ? m[1] : line;
    }
    if (tool === 'elan') {
      // "elan 4.0.0 (....)"
      const m = /elan\s+([\w\.-]+)/i.exec(line); return m ? m[1] : line;
    }
    if (tool === 'lake') {
      // "Lake version x.y.z" (best-effort)
      const m = /Lake(?:\s+version)?\s+([\w\.-]+)/i.exec(line); return m ? m[1] : line;
    }
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
    if (tool === 'kani') {
      const m = /kani(?:-driver)?\s+([\w\.-]+)/i.exec(line); return m ? m[1] : line;
    }
    if (tool === 'cspx') {
      // "cspx 0.1.0"
      const m = /\bcspx\s+([\w\.-]+)/i.exec(line); return m ? m[1] : line;
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

// Kani
const hasKani = has('kani') || has('cargo-kani') || has('kani-driver');
const kaniTool = has('kani') ? 'kani' : (has('cargo-kani') ? 'cargo-kani' : (has('kani-driver') ? 'kani-driver' : ''));
report.push({ tool: 'kani', present: hasKani, version: hasKani ? shortVer('kani', version(kaniTool, ['--version'])) : 'n/a' });

// SPIN
const hasSpin = has('spin');
report.push({ tool: 'spin', present: hasSpin, version: hasSpin ? shortVer('spin', version('spin', ['-V'])) : 'n/a' });

// GCC (pan build)
const hasGcc = has('gcc');
report.push({ tool: 'gcc', present: hasGcc, version: hasGcc ? shortVer('gcc', version('gcc', ['--version'])) : 'n/a' });

// CSP (runner configuration)
const cspRunCmdSet = Boolean((process.env.CSP_RUN_CMD || '').trim());
report.push({ tool: 'CSP_RUN_CMD', present: cspRunCmdSet, path: cspRunCmdSet ? 'set (command hidden)' : 'unset (set CSP_RUN_CMD to run a CSP tool)' });
const hasCspx = has('cspx');
report.push({ tool: 'cspx', present: hasCspx, version: hasCspx ? shortVer('cspx', version('cspx', ['--version'])) : 'n/a' });
const cspxSummaryJson = hasCspx ? supportsSummaryJson() : false;
report.push({
  tool: 'cspx --summary-json',
  present: cspxSummaryJson,
  path: cspxSummaryJson ? 'supported' : 'missing (install pinned cspx with summary contract support)',
});
const hasRefines = has('refines');
report.push({ tool: 'refines', present: hasRefines, version: hasRefines ? shortVer('refines', version('refines', ['--version'])) : 'n/a' });
const hasCspmchecker = has('cspmchecker');
report.push({ tool: 'cspmchecker', present: hasCspmchecker, version: hasCspmchecker ? shortVer('cspmchecker', version('cspmchecker', ['--version'])) : 'n/a' });

// Lean4
const hasElan = has('elan');
report.push({ tool: 'elan', present: hasElan, version: hasElan ? shortVer('elan', version('elan', ['--version'])) : 'n/a' });
const hasLake = has('lake');
report.push({ tool: 'lake', present: hasLake, version: hasLake ? shortVer('lake', version('lake', ['--version'])) : 'n/a' });

console.log('Formal tools status');
for (const r of report) {
  const status = r.present ? '✅' : '❌';
  const extra = r.version ? ` (${r.version})` : (r.path ? ` (${r.path})` : '');
  console.log(`- ${status} ${r.tool}${extra}`);
}

// One-line digest (non-blocking)
try {
  const map = Object.fromEntries(report.map(r => [r.tool, r.present]));
  const vers = Object.fromEntries(report.map(r => [r.tool, r.version || 'n/a']));
  const tlc = !!(process.env.TLA_TOOLS_JAR || '').trim();
  const ap = map['apalache-mc'] ? `yes(${vers['apalache-mc']||'n/a'})` : 'no';
  const z3 = map['z3'] ? `yes(${vers['z3']||'n/a'})` : 'no';
  const c5 = map['cvc5'] ? `yes(${vers['cvc5']||'n/a'})` : 'no';
  const kani = map['kani'] ? `yes(${vers['kani']||'n/a'})` : 'no';
  const spin = map['spin'] ? `yes(${vers['spin']||'n/a'})` : 'no';
  const gcc = map['gcc'] ? `yes(${vers['gcc']||'n/a'})` : 'no';
  const lean = map['lake'] ? `yes(${vers['lake']||'n/a'})` : 'no';
  const csp = map['CSP_RUN_CMD']
    ? 'CSP_RUN_CMD'
    : (map['cspx']
      ? `cspx(${vers['cspx']||'n/a'},summary-json=${map['cspx --summary-json'] ? 'yes' : 'no'})`
      : (map['refines']
        ? `refines(${vers['refines']||'n/a'})`
        : (map['cspmchecker'] ? 'cspmchecker' : 'unset')));
  const jv = vers['java'] || 'n/a';
  const line = [
    `tlc=${tlc?'yes':'no'}`,
    `apalache=${ap}`,
    `z3=${z3}`,
    `cvc5=${c5}`,
    `kani=${kani}`,
    `spin=${spin}`,
    `gcc=${gcc}`,
    `csp=${csp}`,
    `lean=${lean}`,
    `java=${jv}`
  ].join(' ');
  console.log(`Tools: ${line}`);
} catch {}

// Non-blocking: always exit 0
process.exit(0);
