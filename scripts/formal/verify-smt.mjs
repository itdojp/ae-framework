#!/usr/bin/env node
// Lightweight SMT runner: accepts --solver and --file, runs if available, writes a summary. Non-blocking.
import { execSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

function parseArgs(argv) {
  const args = { _: [] };
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--help' || a === '-h') args.help = true;
    else if (a === '--file' && argv[i+1]) { args.file = argv[++i]; }
    else if (a.startsWith('--file=')) { args.file = a.slice(7); }
    else if (a.startsWith('--solver=')) { args.solver = a.slice(9); }
    else { args._.push(a); }
  }
  return args;
}

function has(cmd) { try { execSync(`bash -lc 'command -v ${cmd}'`, {stdio:'ignore'}); return true; } catch { return false; } }
function sh(cmd) { try { return execSync(cmd, { encoding: 'utf8' }); } catch (e) { return (e.stdout?.toString?.() || '') + (e.stderr?.toString?.() || ''); } }

const args = parseArgs(process.argv);
if (args.help) {
  console.log(`Usage: node scripts/formal/verify-smt.mjs [--solver=z3|cvc5] [--file path/to/input.smt2]`);
  process.exit(0);
}

const solver = (args.solver || 'z3').toLowerCase();
const file = args.file;

const repoRoot = path.resolve(process.cwd());
const outDir = path.join(repoRoot, 'hermetic-reports', 'formal');
const outFile = path.join(outDir, 'smt-summary.json');
fs.mkdirSync(outDir, { recursive: true });

let status = 'skipped';
let output = '';
let ran = false;

if (!file) {
  status = 'no_file';
} else if (!fs.existsSync(file)) {
  status = 'file_not_found';
} else if (solver === 'z3' && has('z3')) {
  output = sh(`bash -lc 'z3 -smt2 ${file.replace(/'/g, "'\\''")} 2>&1 || true'`);
  status = 'ran'; ran = true;
} else if (solver === 'cvc5' && has('cvc5')) {
  output = sh(`bash -lc 'cvc5 --lang=smt2 ${file.replace(/'/g, "'\\''")} 2>&1 || true'`);
  status = 'ran'; ran = true;
} else {
  status = 'solver_not_available';
}

const summary = {
  solver,
  file: file || null,
  ran,
  status,
  timestamp: new Date().toISOString(),
  output: output.slice(0, 4000)
};

fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`SMT summary written: ${path.relative(repoRoot, outFile)}`);
console.log(`- solver=${solver} status=${status}${ran ? '' : ''}`);

// Non-blocking
process.exit(0);
