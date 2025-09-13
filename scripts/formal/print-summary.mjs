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
  lines.push(`Conformance: schemaErrors=${ce}, invariantViolations=${iv}, rate=${vr}${first}`);
}
if (f.smt) lines.push(`SMT: ${f.smt.status}`);
if (f.alloy) lines.push(`Alloy: ${f.alloy.status}`);
if (f.tla) lines.push(`TLA: ${f.tla.status} (${f.tla.engine})`);

if (lines.length) {
  console.log('--- Formal Summary ---');
  for (const l of lines) console.log(l);
  console.log('----------------------');
} else {
  console.log('Formal summary is empty');
}
process.exit(0);

