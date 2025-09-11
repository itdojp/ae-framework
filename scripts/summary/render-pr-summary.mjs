#!/usr/bin/env node
import fs from 'node:fs';
function r(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; } }
const mode = process.env.SUMMARY_MODE === 'detailed' ? 'detailed' : 'digest';
const c = r('artifacts/summary/combined.json') || {};
const adaptersArr = (c.adapters||[]);
const adaptersLine = adaptersArr.map(a=>`${a.adapter||a.name}: ${a.summary} (${a.status})`).join(', ');
const adaptersList = adaptersArr.map(a=>`  - ${a.adapter||a.name}: ${a.summary} (${a.status})`).join('\n');
const formalObj = c.formal || r('formal/summary.json') || {};
const formal = formalObj.result || 'n/a';
const replay = c.replay || r('artifacts/domain/replay.summary.json') || {};
const props = c.properties ? (Array.isArray(c.properties) ? c.properties : [c.properties]) : (r('artifacts/properties/summary.json') ? [r('artifacts/properties/summary.json')] : []);
const cov = r('coverage/coverage-summary.json');
let coverageLine = 'Coverage: n/a';
if (cov && cov.total && cov.total.lines && typeof cov.total.lines.pct === 'number') {
  coverageLine = `Coverage: ${cov.total.lines.pct}%`;
}
const traceIds = new Set();
for (const a of adaptersArr) if (a?.traceId) traceIds.add(a.traceId);
if (formalObj?.traceId) traceIds.add(formalObj.traceId);
if (replay?.traceId) traceIds.add(replay.traceId);
for (const p of props) if (p?.traceId) traceIds.add(p.traceId);
const replayLine = replay.totalEvents!==undefined ? `Replay: ${replay.totalEvents} events, ${(replay.violatedInvariants||[]).length} violations` : 'Replay: n/a';
let md;
if (mode === 'digest') {
  md = `${coverageLine} | Formal: ${formal} | ${replayLine} | Adapters: ${adaptersLine} | Trace: ${Array.from(traceIds).join(', ')}`;
} else {
  md = `## Quality Summary\n- ${coverageLine}\n- Adapters:\n${adaptersList}\n- Formal: ${formal}\n- ${replayLine}\n- Trace IDs: ${Array.from(traceIds).join(', ')}`;
}
fs.mkdirSync('artifacts/summary',{recursive:true});
fs.writeFileSync('artifacts/summary/PR_SUMMARY.md', md);
console.log(md);
