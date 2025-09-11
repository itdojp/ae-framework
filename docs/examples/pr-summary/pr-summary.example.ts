// PR Summary Aggregator (Example)
// Reads normalized artifacts and prints a Markdown summary
// Docs-only example; not wired into build.
import fs from 'node:fs';
import path from 'node:path';

function readJson(p: string) {
  try { return JSON.parse(fs.readFileSync(p, 'utf-8')); } catch { return undefined; }
}

function glob(dir: string): string[] {
  try { return fs.readdirSync(dir).map(f => path.join(dir, f)).filter(p => fs.statSync(p).isFile()); } catch { return []; }
}

const adapterSummaries = glob('artifacts').flatMap(d =>
  fs.existsSync(d) ? glob(d).filter(p => /summary\.json$/.test(p)) : []
).map(readJson).filter(Boolean) as any[];

const formal = readJson('formal/summary.json');
const properties = readJson('artifacts/properties/summary.json');

const adaptersLine = adapterSummaries.map(a => `${a.adapter}: ${a.summary} (${a.status})`).join('\n  - ');
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
