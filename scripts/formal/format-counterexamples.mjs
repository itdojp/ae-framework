#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function readJson(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; } }

function toGWT(ce){
  if (!ce) return '';
  const given = ce.json?.given ? `Given ${JSON.stringify(ce.json.given)}` : '';
  const when = ce.json?.when ? `\nWhen ${JSON.stringify(ce.json.when)}` : '';
  const then = ce.json?.then?.violated ? `\nThen invariant \"${ce.json.then.violated}\" fails` : (ce.property ? `\nThen property \"${ce.property}\" fails` : '');
  return `${given}${when}${then}`.trim();
}

const formal = readJson('formal/summary.json');
if (!formal) {
  console.error('No formal/summary.json found');
  process.exit(0);
}
const lines=[]; const items=[];
for (const ce of (formal.counterexamples||[])){
  const gwt = toGWT(ce);
  if (gwt) lines.push(gwt);
  items.push({ property: ce.property, gwt, json: ce.json });
}
fs.mkdirSync(path.dirname('artifacts/formal/gwt.txt'), { recursive: true });
fs.writeFileSync('artifacts/formal/gwt.txt', lines.join('\n\n'));
fs.writeFileSync('artifacts/formal/gwt.summary.json', JSON.stringify({ items }, null, 2));
console.log('✓ Wrote artifacts/formal/gwt.txt and artifacts/formal/gwt.summary.json');
