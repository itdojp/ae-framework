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
const formalObj = c.formal || r('formal/summary.json') || r('hermetic-reports/formal/summary.json') || {};
const formalHerm = r('hermetic-reports/formal/summary.json') || {};
const formalAgg = r('artifacts/formal/formal-aggregate.json') || {};
const formal = formalObj.result || t('n/a','不明');
const gwt = r('artifacts/formal/gwt.summary.json');
const gwtItems = gwt?.items || [];
const gwtCount = gwtItems.length;
const gwtFirst = gwtCount ? (gwtItems[0].property || (gwtItems[0].gwt ? String(gwtItems[0].gwt).split('\n')[0] : '')) : '';
const replay = c.replay || r('artifacts/domain/replay.summary.json') || {};
const bdd = c.bdd || r('artifacts/bdd/scenarios.json') || {};
const props = c.properties ? (Array.isArray(c.properties) ? c.properties : [c.properties]) : (r('artifacts/properties/summary.json') ? [r('artifacts/properties/summary.json')] : []);
const cov = r('coverage/coverage-summary.json');
const ltlSug = r('artifacts/properties/ltl-suggestions.json');
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
// Properties (PBT) quick count: prefer aggregate 'count' or fallback to array length
let propsCount = 0;
if (Array.isArray(props) && props.length) {
  for (const p of props) {
    if (p && typeof p.count === 'number') {
      propsCount += p.count;
    } else {
      propsCount += 1;
    }
  }
}
const propsLine = propsCount
  ? t(`Props: ${propsCount}`, `プロパティ: ${propsCount}`)
  : t('Props: n/a','プロパティ: なし');
const ltlLine = ltlSug && typeof ltlSug.count === 'number'
  ? t(`LTL sugg: ${ltlSug.count}`, `LTL候補: ${ltlSug.count}`)
  : t('LTL sugg: n/a', 'LTL候補: なし');
const adapterCountsLine = t(
  `Adapters ok/warn/err=${statusCounts.ok||0}/${statusCounts.warn||0}/${statusCounts.error||0}`,
  `アダプタ 正常/注意/失敗=${statusCounts.ok||0}/${statusCounts.warn||0}/${statusCounts.error||0}`
);
const gwtLine = gwtCount 
  ? t(`GWT: ${gwtCount} (e.g., ${gwtFirst})`, `GWT: ${gwtCount}（例: ${gwtFirst}）`)
  : t('GWT: 0','GWT: 0');
const bddLine = bdd && (bdd.criteriaCount!==undefined || bdd.title)
  ? t(`BDD: ${bdd.criteriaCount ?? '?'} criteria (${bdd.title ?? 'Feature'})`, `BDD: 受入基準 ${bdd.criteriaCount ?? '?'}（${bdd.title ?? 'Feature'}）`)
  : t('BDD: n/a','BDD: なし');
// Alloy temporal (from aggregate JSON if present)
let alloyTemporalLine = '';
try {
  const temp = formalAgg?.info?.temporal?.alloy;
  if (temp && (temp.present || (Array.isArray(temp.operators) && temp.operators.length))) {
    const ops = Array.isArray(temp.operators) ? temp.operators.join(', ') : '';
    const pops = Array.isArray(temp.pastOperators) ? temp.pastOperators.join(', ') : '';
    alloyTemporalLine = t(
      `Alloy temporal: present=${!!temp.present}${ops? ` ops=[${ops}]`:''}${pops? ` past=[${pops}]`:''}`,
      `Alloy時相: present=${!!temp.present}${ops? ` ops=[${ops}]`:''}${pops? ` past=[${pops}]`:''}`
    );
  }
} catch {}
const alerts=[];
if ((statusCounts.error||0) > errorMax) alerts.push(t(`adapter errors>${errorMax}`, `アダプタ失敗>${errorMax}`));
if ((statusCounts.warn||0) > warnMax) alerts.push(t(`adapter warnings>${warnMax}`, `アダプタ注意>${warnMax}`));
const alertsLine = alerts.length ? t(`Alerts: ${alerts.join(', ')}`, `警告: ${alerts.join(', ')}`) : t('Alerts: none','警告: なし');
// Conformance short line (violationRate / hooks matchRate)
let conformanceLine = '';
try {
  const conf = (formalAgg?.conformance) || (r('hermetic-reports/formal/summary.json')?.conformance) || {};
  const vr = (typeof conf.violationRate === 'number') ? conf.violationRate : null;
  const mr = (typeof formalAgg?.info?.conformance?.hookReplayMatchRate === 'number')
    ? formalAgg.info.conformance.hookReplayMatchRate
    : (typeof conf?.runtimeHooksCompare?.matchRate === 'number' ? conf.runtimeHooksCompare.matchRate : null);
  const onlyH = (typeof formalAgg?.info?.conformance?.onlyHooksCount === 'number') ? formalAgg.info.conformance.onlyHooksCount : null;
  const onlyT = (typeof formalAgg?.info?.conformance?.onlyTraceCount === 'number') ? formalAgg.info.conformance.onlyTraceCount : null;
  const hEv = (typeof formalAgg?.info?.conformance?.hookEvents === 'number') ? formalAgg.info.conformance.hookEvents : null;
  const tEv = (typeof formalAgg?.info?.conformance?.traceEvents === 'number') ? formalAgg.info.conformance.traceEvents : null;
  const delta = (onlyH!==null || onlyT!==null) ? ` Δ(hooks=${onlyH ?? 'n/a'}/trace=${onlyT ?? 'n/a'})` : '';
  const evs = (hEv!==null || tEv!==null) ? ` ev(h=${hEv ?? 'n/a'}/t=${tEv ?? 'n/a'})` : '';
  if (vr !== null || mr !== null) {
    const en = `Conf: rate=${vr ?? 'n/a'}${mr!==null? ` match=${mr}`:''}${delta}${evs}`;
    const ja = `適合: 率=${vr ?? 'n/a'}${mr!==null? ` 一致率=${mr}`:''}${delta}${evs}`;
    conformanceLine = t(en, ja);
  }
} catch {}

let md;
if (mode === 'digest') {
  md = `${coverageLine} | ${alertsLine} | ${t('Formal','フォーマル')}: ${formal}${alloyTemporalLine? ` | ${alloyTemporalLine}`:''}${conformanceLine? ` | ${conformanceLine}`:''} | ${bddLine} | ${ltlLine} | ${gwtLine} | ${adapterCountsLine} | ${adaptersLine} | ${replayLine} | ${t('Trace','トレース')}: ${Array.from(traceIds).join(', ')}`;
} else {
  md = `## ${t('Quality Summary','品質サマリ')}\n- ${coverageLine}\n- ${alertsLine}\n- ${t('Formal','フォーマル')}: ${formal}\n${alloyTemporalLine? `- ${alloyTemporalLine}\n`:''}${conformanceLine? `- ${conformanceLine}\n`:''}- ${adapterCountsLine}\n- ${t('Adapters','アダプタ')}:\n${adaptersList}\n- ${bddLine}\n- ${ltlLine}\n- ${gwtLine}\n- ${replayLine}\n- ${t('Trace IDs','トレースID')}: ${Array.from(traceIds).join(', ')}`;
}
// Fallback: if formal is n/a, print presentCount from aggregate JSON
try {
  if ((formal === 'n/a' || formal === '不明') && formalAgg?.info && typeof formalAgg.info.presentCount === 'number') {
    const pc = Number(formalAgg.info.presentCount || 0);
    const presentKeys = Object.entries(formalAgg.info.present || {}).filter(([,v])=>v).map(([k])=>k).join(', ');
    const line = t(`Formal: present ${pc}/5${pc? ` (${presentKeys})`:''}`, `フォーマル: present ${pc}/5${pc? `（${presentKeys}）`:''}`);
    if (mode === 'digest') md += ` | ${line}`; else md += `\n- ${line}`;
  }
} catch {}

// (Removed duplicate conformance fallback line; unified above using aggregate JSON)
fs.mkdirSync('artifacts/summary',{recursive:true});
fs.writeFileSync('artifacts/summary/PR_SUMMARY.md', md);
console.log(md);
