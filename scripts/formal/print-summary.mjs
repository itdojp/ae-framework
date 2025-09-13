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
  const conformanceLine = `Conformance: schemaErrors=${ce}, invariantViolations=${iv}, rate=${vr}${first}${typeBreak}`;
  const colored = (iv === 0 && ce === 0) ? c.green(conformanceLine) : c.yellow(conformanceLine);
  lines.push(colored);
}
if (f.smt) {
  const st = f.smt.status;
  const smtLine = `SMT: ${st}`;
  lines.push(st === 'ran' ? c.green(smtLine) : (st === 'solver_not_available' ? c.gray(smtLine) : c.yellow(smtLine)));
}
if (f.alloy) {
  const st = f.alloy.status;
  const alloyLine = `Alloy: ${st}`;
  lines.push(st === 'ran' ? c.green(alloyLine) : (st === 'tool_not_available' ? c.gray(alloyLine) : c.yellow(alloyLine)));
}
if (f.tla) {
  const st = f.tla.status;
  const tlaLine = `TLA: ${st} (${f.tla.engine})`;
  lines.push(st === 'ran' ? c.green(tlaLine) : (st === 'tool_not_available' ? c.gray(tlaLine) : c.yellow(tlaLine)));
}

if (lines.length) {
  console.log(c.bold('--- Formal Summary ---'));
  for (const l of lines) console.log(l);
  console.log(c.bold('----------------------'));
} else {
  console.log('Formal summary is empty');
}
process.exit(0);
