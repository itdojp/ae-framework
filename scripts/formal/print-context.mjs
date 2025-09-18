#!/usr/bin/env node
// Print formal run context (branch/commit/time + tools presence/defaults). Non-blocking.
import { execSync } from 'node:child_process';

function tryCmd(cmd){ try { return execSync(cmd, {encoding:'utf8'}).trim(); } catch { return ''; } }
function has(cmd){ try { execSync(`bash -lc 'command -v ${cmd}'`, {stdio:'ignore'}); return true; } catch { return false; } }
function ver(cmd, args=['--version']){ try { return execSync(`bash -lc '${cmd} ${args.join(' ')}'`, {encoding:'utf8'}).trim(); } catch { return ''; } }
function short(tool, raw){
  if (!raw) return '';
  const line = String(raw).split('\n')[0];
  try {
    if (tool==='z3') { const m=/Z3 version\s+([\w\.-]+)/i.exec(line); return m?m[1]:line; }
    if (tool==='cvc5') { const m=/cvc5\s+([\w\.-]+)/i.exec(line); return m?m[1]:line; }
    if (tool==='apalache') { const m=/version\s+([\w\.-]+)/i.exec(line); return m?m[1]:line; }
    if (tool==='java') { const m=/version\s+"([\w\.-]+)"/i.exec(line); return m?m[1]:line; }
    return line;
  } catch { return line; }
}

const branch = tryCmd("bash -lc 'git rev-parse --abbrev-ref HEAD'") || process.env.GITHUB_REF_NAME || 'unknown';
const commit = tryCmd("bash -lc 'git rev-parse --short HEAD'") || (process.env.GITHUB_SHA ? process.env.GITHUB_SHA.slice(0,7) : 'unknown');
const when = new Date().toISOString();

// Tool presence
const hasApalache = has('apalache-mc');
const hasZ3 = has('z3');
const hasCvc5 = has('cvc5');
const hasTlc = !!(process.env.TLA_TOOLS_JAR || '').trim();
const vZ3 = hasZ3 ? short('z3', ver('z3', ['--version'])) : '';
const vCvc5 = hasCvc5 ? short('cvc5', ver('cvc5', ['--version'])) : '';
const vAp = hasApalache ? short('apalache', ver('apalache-mc', ['version'])) : '';
const vJava = has('java') ? short('java', ver('java', ['-version'])) : '';

// Defaults used by verify-lite flow
const defaultTla = 'tlc';
const defaultSmt = 'cvc5';

console.log(`Formal run context: branch=${branch} commit=${commit} time=${when}`);
console.log(`Tools: tlc=${hasTlc?'yes':'no'} apalache=${hasApalache?('yes('+vAp+')'):'no'} z3=${hasZ3?('yes('+vZ3+')'):'no'} cvc5=${hasCvc5?('yes('+vCvc5+')'):'no'} java=${vJava||'n/a'}`);
console.log(`Defaults: tla=${defaultTla} smt=${defaultSmt}`);
process.exit(0);
