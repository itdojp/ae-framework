#!/usr/bin/env node
// Lightweight TLA runner: accepts --engine and --file, tries to run Apalache or TLC if available; writes a summary. Non-blocking.
import { execSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

function parseArgs(argv){
  const args = { _: [] };
  for (let i=2;i<argv.length;i++){
    const a=argv[i];
    if (a==='-h'||a==='--help') args.help=true;
    else if (a.startsWith('--engine=')) { args.engine=a.slice(9); }
    else if ((a==='--engine' || a==='-e') && argv[i+1]) { args.engine=argv[++i]; }
    else if (a.startsWith('--file=')) { args.file=a.slice(7); }
    else if (a==='--file' && argv[i+1]) { args.file=argv[++i]; }
    else { args._.push(a); }
  }
  return args;
}

function has(cmd){ try { execSync(`bash -lc 'command -v ${cmd}'`, {stdio:'ignore'}); return true; } catch { return false; } }
function sh(cmd){ try { return execSync(cmd, {encoding:'utf8'}); } catch(e){ return (e.stdout?.toString?.()||'') + (e.stderr?.toString?.()||''); } }

const args = parseArgs(process.argv);
const timeoutSec = args.timeout ? Math.max(1, Math.floor(Number(args.timeout)/1000)) : 0;
function has(cmd){ try { execSync(`bash -lc 'command -v ${cmd}'`, {stdio:'ignore'}); return true; } catch { return false; } }
const haveTimeout = has('timeout');
if (args.help){
  console.log(`Usage: node scripts/formal/verify-tla.mjs [--engine=tlc|apalache] [--file spec/tla/DomainSpec.tla] [--timeout <ms>]`);
  console.log('See docs/quality/formal-tools-setup.md for TLC/Apalache setup.');
  process.exit(0);
}

const engine = (args.engine || 'tlc').toLowerCase();
const repoRoot = process.cwd();
const file = args.file || path.join('spec','tla','DomainSpec.tla');
const absFile = path.resolve(repoRoot, file);

const outDir = path.join(repoRoot, 'hermetic-reports', 'formal');
const outFile = path.join(outDir, 'tla-summary.json');
fs.mkdirSync(outDir, { recursive: true });

let ran = false;
let status = 'skipped';
let output = '';

if (!fs.existsSync(absFile)){
  status = 'file_not_found';
  output = `TLA file not found: ${absFile}`;
} else if (engine === 'apalache'){
  if (has('apalache-mc')){
    const base = `apalache-mc check --inv=Invariant ${absFile.replace(/'/g, "'\\''")}`;
    const cmd = timeoutSec && haveTimeout ? `timeout ${timeoutSec}s ${base}` : base;
    output = sh(`bash -lc '${cmd} 2>&1 || true'`);
    ran = true; status = 'ran';
  } else {
    status = 'tool_not_available';
    output = 'Apalache not found. See docs/quality/formal-tools-setup.md';
  }
} else {
  // TLC via TLA_TOOLS_JAR
  if (process.env.TLA_TOOLS_JAR){
    const jar = process.env.TLA_TOOLS_JAR;
    const base = `java -cp ${jar} tlc2.TLC ${absFile.replace(/'/g, "'\\''")}`;
    const cmd = timeoutSec && haveTimeout ? `timeout ${timeoutSec}s ${base}` : base;
    output = sh(`bash -lc '${cmd} 2>&1 || true'`);
    ran = true; status = 'ran';
  } else {
    status = 'tool_not_available';
    output = 'TLC not available (TLA_TOOLS_JAR not set). See docs/quality/formal-tools-setup.md';
  }
}

const summary = {
  engine,
  file: path.relative(repoRoot, absFile),
  ran,
  status,
  timestamp: new Date().toISOString(),
  output: output.slice(0, 4000)
};
fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`TLA summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- engine=${engine} file=${summary.file} status=${status}`);

// Non-blocking
process.exit(0);
