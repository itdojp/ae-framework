// PR Summary Aggregator (Example)
// Mirrors the current renderer contract at a high level.
// Prefer combined.json, then fallback inputs where the live renderer does.
import fs from 'node:fs';
import path from 'node:path';

function readJson(p: string) {
  try { return JSON.parse(fs.readFileSync(p, 'utf-8')); } catch { return undefined; }
}

function glob(dir: string): string[] {
  try { return fs.readdirSync(dir).map(f => path.join(dir, f)).filter(p => fs.statSync(p).isFile()); } catch { return []; }
}

const combined = readJson('artifacts/summary/combined.json') || {};
const adapterSummaries = Array.isArray(combined.adapters) ? combined.adapters : [];

const formal = combined.formal
  || readJson('formal/summary.json')
  || readJson('artifacts/hermetic-reports/formal/summary.json');
const properties = combined.properties || readJson('artifacts/properties/summary.json');

const adaptersLine = adapterSummaries.map(a => `${a.adapter || a.name}: ${a.summary} (${a.status})`).join('\n  - ');
const formalLine = formal ? `${formal.result}` : 'n/a';

const traceIds = new Set<string>();
for (const a of adapterSummaries) if (a.traceId) traceIds.add(a.traceId);
if (formal?.traceId) traceIds.add(formal.traceId);
if (properties) {
  const arr = Array.isArray(properties) ? properties : [properties];
  for (const p of arr) if (p.traceId) traceIds.add(p.traceId);
}

const md = `## Quality Summary\n- Adapters:\n  - ${adaptersLine}\n- Formal: ${formalLine}\n- Trace IDs: ${Array.from(traceIds).join(', ')}`;

console.log(md);
