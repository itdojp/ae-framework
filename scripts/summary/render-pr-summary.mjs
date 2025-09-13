#!/usr/bin/env node
import fs from 'node:fs';
function r(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; } }
const lang = (process.env.SUMMARY_LANG||'en').toLowerCase();
const t = (en, ja) => (lang==='ja'? ja : en);
const mode = process.env.SUMMARY_MODE === 'detailed' ? 'detailed' : 'digest';
const warnMax = isFinite(Number(process.env.ADAPTER_WARN_MAX)) ? Number(process.env.ADAPTER_WARN_MAX) : 0;
const errorMax = isFinite(Number(process.env.ADAPTER_ERROR_MAX)) ? Number(process.env.ADAPTER_ERROR_MAX) : 0;
const c = r('artifacts/summary/combined.json') || {};
const adaptersArr = (c.adapters||[]);
const statusCounts = adaptersArr.reduce((acc,a)=>{ const s=(a.status||'ok').toLowerCase(); acc[s]=(acc[s]||0)+1; return acc; },{});
const adaptersLine = adaptersArr.map(a=>`${a.adapter||a.name}: ${a.summary} (${a.status})`).join(', ');
const adaptersList = adaptersArr.map(a=>`  - ${a.adapter||a.name}: ${a.summary} (${a.status})`).join('\n');
const formalObj = c.formal || r('formal/summary.json') || {};
const formal = formalObj.result || t('n/a','不明');
const gwt = r('artifacts/formal/gwt.summary.json');
const gwtItems = gwt?.items || [];
const gwtCount = gwtItems.length;
const gwtFirst = gwtCount ? (gwtItems[0].property || (gwtItems[0].gwt ? String(gwtItems[0].gwt).split('\n')[0] : '')) : '';
const replay = c.replay || r('artifacts/domain/replay.summary.json') || {};
const bdd = c.bdd || r('artifacts/bdd/scenarios.json') || {};
const props = c.properties ? (Array.isArray(c.properties) ? c.properties : [c.properties]) : (r('artifacts/properties/summary.json') ? [r('artifacts/properties/summary.json')] : []);
const cov = r('coverage/coverage-summary.json');
let coverageLine = t('Coverage: n/a','カバレッジ: 不明');
if (cov?.total?.lines && typeof cov.total.lines.pct === 'number') coverageLine = t(`Coverage: ${cov.total.lines.pct}%`, `カバレッジ: ${cov.total.lines.pct}%`);
const traceIds = new Set();
for (const a of adaptersArr) if (a?.traceId) traceIds.add(a.traceId);
if (formalObj?.traceId) traceIds.add(formalObj.traceId);
if (replay?.traceId) traceIds.add(replay.traceId);
for (const p of props) if (p?.traceId) traceIds.add(p.traceId);
const replayLine = replay.totalEvents!==undefined 
  ? t(`Replay: ${replay.totalEvents} events, ${(replay.violatedInvariants||[]).length} violations`, `リプレイ: ${replay.totalEvents}件, 違反 ${(replay.violatedInvariants||[]).length}件`)
  : t('Replay: n/a','リプレイ: なし');
const adapterCountsLine = t(
  `Adapters: ok=${statusCounts.ok||0}, warn=${statusCounts.warn||0}, error=${statusCounts.error||0}`,
  `アダプタ: 正常=${statusCounts.ok||0}, 注意=${statusCounts.warn||0}, 失敗=${statusCounts.error||0}`
);
const gwtLine = gwtCount 
  ? t(`GWT: ${gwtCount} (e.g., ${gwtFirst})`, `GWT: ${gwtCount}（例: ${gwtFirst}）`)
  : t('GWT: 0','GWT: 0');
const bddLine = bdd && (bdd.criteriaCount!==undefined || bdd.title)
  ? t(`BDD: ${bdd.criteriaCount ?? '?'} criteria (${bdd.title ?? 'Feature'})`, `BDD: 受入基準 ${bdd.criteriaCount ?? '?'}（${bdd.title ?? 'Feature'}）`)
  : t('BDD: n/a','BDD: なし');
const alerts=[];
if ((statusCounts.error||0) > errorMax) alerts.push(t(`adapter errors>${errorMax}`, `アダプタ失敗>${errorMax}`));
if ((statusCounts.warn||0) > warnMax) alerts.push(t(`adapter warnings>${warnMax}`, `アダプタ注意>${warnMax}`));
const alertsLine = alerts.length ? t(`Alerts: ${alerts.join(', ')}`, `警告: ${alerts.join(', ')}`) : t('Alerts: none','警告: なし');
let md;
if (mode === 'digest') {
  md = `${coverageLine} | ${alertsLine} | ${t('Formal','フォーマル')}: ${formal} | ${replayLine} | ${bddLine} | ${gwtLine} | ${adapterCountsLine} | ${adaptersLine} | ${t('Trace','トレース')}: ${Array.from(traceIds).join(', ')}`;
} else {
  md = `## ${t('Quality Summary','品質サマリ')}\n- ${coverageLine}\n- ${alertsLine}\n- ${gwtLine}\n- ${bddLine}\n- ${adapterCountsLine}\n- ${t('Adapters','アダプタ')}:\n${adaptersList}\n- ${t('Formal','フォーマル')}: ${formal}\n- ${replayLine}\n- ${t('Trace IDs','トレースID')}: ${Array.from(traceIds).join(', ')}`;
}
fs.mkdirSync('artifacts/summary',{recursive:true});
fs.writeFileSync('artifacts/summary/PR_SUMMARY.md', md);
console.log(md);
