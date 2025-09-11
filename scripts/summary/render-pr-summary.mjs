#!/usr/bin/env node
import fs from 'node:fs';
function r(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; } }
const mode = process.env.SUMMARY_MODE === 'detailed' ? 'detailed' : 'digest';
const c = r('artifacts/summary/combined.json') || {};
const adaptersArr = (c.adapters||[]);
const statusCounts = adaptersArr.reduce((acc,a)=>{ const s=(a.status||'ok').toLowerCase(); acc[s]=(acc[s]||0)+1; return acc; },{});
const adaptersLine = adaptersArr.map(a=>`${a.adapter||a.name}: ${a.summary} (${a.status})`).join(', ');
const adaptersList = adaptersArr.map(a=>`  - ${a.adapter||a.name}: ${a.summary} (${a.status})`).join('\n');
const formalObj = c.formal || r('formal/summary.json') || {};
const formal = formalObj.result || 'n/a';
const gwt = r('artifacts/formal/gwt.summary.json');
const gwtItems = gwt?.items || [];
const gwtCount = gwtItems.length;
const gwtFirst = gwtCount ? (gwtItems[0].property || (gwtItems[0].gwt ? String(gwtItems[0].gwt).split('\n')[0] : '')) : '';
const replay = c.replay || r('artifacts/domain/replay.summary.json') || {};
const props = c.properties ? (Array.isArray(c.properties) ? c.properties : [c.properties]) : (r('artifacts/properties/summary.json') ? [r('artifacts/properties/summary.json')] : []);
const cov = r('coverage/coverage-summary.json');
let coverageLine = 'Coverage: n/a';
if (cov?.total?.lines && typeof cov.total.lines.pct === 'number') coverageLine = `Coverage: ${cov.total.lines.pct}%`;
const traceIds = new Set();
for (const a of adaptersArr) if (a?.traceId) traceIds.add(a.traceId);
if (formalObj?.traceId) traceIds.add(formalObj.traceId);
if (replay?.traceId) traceIds.add(replay.traceId);
for (const p of props) if (p?.traceId) traceIds.add(p.traceId);
const replayLine = replay.totalEvents!==undefined ? `Replay: ${replay.totalEvents} events, ${(replay.violatedInvariants||[]).length} violations` : 'Replay: n/a';
const adapterCountsLine = `Adapters: ok=${statusCounts.ok||0}, warn=${statusCounts.warn||0}, error=${statusCounts.error||0}`;
const gwtLine = gwtCount ? `GWT: ${gwtCount} (e.g., ${gwtFirst})` : 'GWT: 0';
let md;
if (mode === 'digest') {
  md = `${coverageLine} | Formal: ${formal} | ${replayLine} | ${gwtLine} | ${adapterCountsLine} | ${adaptersLine} | Trace: ${Array.from(traceIds).join(', ')}`;
} else {
  md = `## Quality Summary\n- ${coverageLine}\n- ${gwtLine}\n- ${adapterCountsLine}\n- Adapters:\n${adaptersList}\n- Formal: ${formal}\n- ${replayLine}\n- Trace IDs: ${Array.from(traceIds).join(', ')}`;
}
fs.mkdirSync('artifacts/summary',{recursive:true});
fs.writeFileSync('artifacts/summary/PR_SUMMARY.md', md);
console.log(md);
