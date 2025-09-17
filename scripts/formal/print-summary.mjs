#!/usr/bin/env node
// Print a concise formal summary to console (non-blocking)
import fs from 'node:fs';
import path from 'node:path';

const repoRoot = process.cwd();
const p = path.join(repoRoot, 'hermetic-reports', 'formal', 'summary.json');
if (!fs.existsSync(p)) {
  console.log('No formal summary found (hermetic-reports/formal/summary.json)');
  process.exit(0);
}
// Allow suppressing console summary via QUIET env
if (process.env.QUIET && process.env.QUIET !== '0' && process.env.QUIET.toLowerCase() !== 'false') {
  process.exit(0);
}
const f = JSON.parse(fs.readFileSync(p,'utf8'));

// Color helpers (respect NO_COLOR)
const useColor = process.stdout.isTTY && !process.env.NO_COLOR;
const c = {
  green: (s) => useColor ? `\u001b[32m${s}\u001b[0m` : s,
  yellow: (s) => useColor ? `\u001b[33m${s}\u001b[0m` : s,
  red: (s) => useColor ? `\u001b[31m${s}\u001b[0m` : s,
  cyan: (s) => useColor ? `\u001b[36m${s}\u001b[0m` : s,
  gray: (s) => useColor ? `\u001b[90m${s}\u001b[0m` : s,
  bold: (s) => useColor ? `\u001b[1m${s}\u001b[0m` : s,
};

const lines = [];
if (f.conformance) {
  const ce = f.conformance.schemaErrors ?? 'n/a';
  const iv = f.conformance.invariantViolations ?? 'n/a';
  const vr = (f.conformance.violationRate !== undefined) ? f.conformance.violationRate : 'n/a';
  let first = '';
  try {
    const fv = f.conformance.firstInvariantViolation;
    if (fv && (fv.index !== undefined) && fv.type) first = `, first=${fv.type}@${fv.index}`;
  } catch {}
  // byType breakdown (optional)
  let typeBreak = '';
  try {
    const bt = f.conformance.byType || {};
    const parts = Object.entries(bt).filter(([,v]) => typeof v === 'number' && v > 0).map(([k,v]) => `${k}=${v}`);
    if (parts.length) typeBreak = `, byType(${parts.join(', ')})`;
  } catch {}
  const ok = (iv === 0 && ce === 0);
  const tag = ok ? c.green('[OK]') : c.yellow('[WARN]');
  const conformanceLine = `${tag} Conformance: schemaErrors=${ce}, invariantViolations=${iv}, rate=${vr}${first}${typeBreak}`;
  lines.push(conformanceLine);
}
if (f.smt) {
  const st = f.smt.status;
  const tag = (st === 'ran') ? c.green('[OK]') : (st === 'solver_not_available' ? c.gray('[INFO]') : c.yellow('[WARN]'));
  const smtLine = `${tag} SMT: ${st}`;
  lines.push(smtLine);
}
if (f.alloy) {
  const st = f.alloy.status;
  const tag = (st === 'ran') ? c.green('[OK]') : (st === 'tool_not_available' ? c.gray('[INFO]') : c.yellow('[WARN]'));
  const alloyLine = `${tag} Alloy: ${st}`;
  lines.push(alloyLine);
  try {
    if (f.alloy.temporal && (Array.isArray(f.alloy.temporal.operators) || Array.isArray(f.alloy.temporal.pastOperators))) {
      const ops = (f.alloy.temporal.operators || []).join(', ');
      const pops = (f.alloy.temporal.pastOperators || []).join(', ');
      const tline = c.cyan(`  - temporal: present=${!!f.alloy.temporal.present}`) + (ops? `, ops=[${ops}]`:'') + (pops? `, past=[${pops}]`:'');
      lines.push(tline);
    }
  } catch {}
}
if (f.tla) {
  const st = f.tla.status;
  const tag = (st === 'ran') ? c.green('[OK]') : (st === 'tool_not_available' ? c.gray('[INFO]') : c.yellow('[WARN]'));
  const tlaLine = `${tag} TLA: ${st} (${f.tla.engine})`;
  lines.push(tlaLine);
}

if (lines.length) {
  console.log(c.bold('--- Formal Summary ---'));
  for (const l of lines) console.log(l);
  console.log(c.bold('----------------------'));
} else {
  console.log('Formal summary is empty');
}
process.exit(0);
