#!/usr/bin/env node
// Example: Convert artifacts/summary/combined.json to a Markdown summary
import fs from 'node:fs';
function r(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; } }
const c = r('artifacts/summary/combined.json') || {};
const adapters=(c.adapters||[]).map(a=>`  - ${a.adapter||a.name}: ${a.summary} (${a.status})`).join('\n');
const formal = c.formal ? (c.formal.result || 'n/a') : 'n/a';
const props = c.properties ? (Array.isArray(c.properties) ? c.properties : [c.properties]) : [];
const traceIds = new Set();
for (const a of c.adapters||[]) if (a.traceId) traceIds.add(a.traceId);
if (c.formal?.traceId) traceIds.add(c.formal.traceId);
for (const p of props) if (p.traceId) traceIds.add(p.traceId);
const md = `## Quality Summary\n- Adapters:\n${adapters}\n- Formal: ${formal}\n- Trace IDs: ${Array.from(traceIds).join(', ')}`;
console.log(md);
