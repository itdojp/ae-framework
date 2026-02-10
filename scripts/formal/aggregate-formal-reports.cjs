#!/usr/bin/env node
// NOTE: moved from .github/workflows/formal-aggregate.yml inline script.
// Keep behavior consistent for CI and PR comments.

const fs=require("fs"), path=require("path");
function rj(p){ try { return JSON.parse(fs.readFileSync(p,"utf-8")); } catch { return undefined; } }
function find(dir, name){ try { const p = path.join(dir, name); return fs.existsSync(p) ? p : undefined; } catch { return undefined; } }
const LINE_CLAMP = parseInt(process.env.FORMAL_AGG_LINE_CLAMP || '200', 10);
const ERRORS_LIMIT = parseInt(process.env.FORMAL_AGG_ERRORS_LIMIT || '5', 10);
function escMd(s){
  if (!s) return '';
  // Basic Markdown escaping to avoid breaking PR rendering
  return String(s)
    .replace(/`/g, "`\u200b")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;");
}
function clamp(s, n=LINE_CLAMP){ s = String(s||''); return s.length>n ? (s.slice(0,n)+"…") : s; }
const base = "artifacts_dl";
const outDir = "artifacts/formal"; fs.mkdirSync(outDir,{recursive:true});
const outMd = path.join(outDir, "formal-aggregate.md");
const outJson = path.join(outDir, "formal-aggregate.json");
const GENERATED_AT = new Date().toISOString();

const modelJson = find(base, "model-check-results/model-check.json");
const alloy = modelJson ? (rj(modelJson)?.alloy || {}) : {};
const tlc = modelJson ? (rj(modelJson)?.tlc || {}) : {};
const alloyOk = Array.isArray(alloy.results) ? alloy.results.filter(x=>x?.ok===true).length : 0;
const alloyTotal = Array.isArray(alloy.results) ? alloy.results.filter(x=>x?.ok!==undefined).length : 0;
const tlcOk = Array.isArray(tlc.results) ? tlc.results.filter(x=>x?.ok===true).length : 0;
const tlcTotal = Array.isArray(tlc.results) ? tlc.results.length : 0;

const tlaSum = find(base, "formal-reports-tla/tla-summary.json");
const alloySum = find(base, "formal-reports-alloy/alloy-summary.json");
const smtSum = find(base, "formal-reports-smt/smt-summary.json");
const apalacheSum = find(base, "formal-reports-apalache/apalache-summary.json");
const apalacheOut = find(base, "formal-reports-apalache/apalache-output.txt");
const confSum = find(base, "formal-reports-conformance/conformance-summary.json");
const kaniSum = find(base, "formal-reports-kani/kani-summary.json");
const spinSum = find(base, "formal-reports-spin/spin-summary.json");
const cspSum = find(base, "formal-reports-csp/csp-summary.json");
const leanSum = find(base, "formal-reports-lean/lean-summary.json");

const apalache = apalacheSum ? rj(apalacheSum) : undefined;
const tla = tlaSum ? rj(tlaSum) : undefined;
const smt = smtSum ? rj(smtSum) : undefined;
const alloyS = alloySum ? rj(alloySum) : undefined;
const conf = confSum ? rj(confSum) : undefined;
const kani = kaniSum ? rj(kaniSum) : undefined;
const spin = spinSum ? rj(spinSum) : undefined;
const csp = cspSum ? rj(cspSum) : undefined;
const lean = leanSum ? rj(leanSum) : undefined;
const clampInfo = {
  lineClamp: process.env.FORMAL_AGG_LINE_CLAMP || '200',
  errorsLimit: process.env.FORMAL_AGG_ERRORS_LIMIT || '5'
};

const lines = [];
lines.push("## 🔎 Formal Reports Aggregate");
lines.push("");
lines.push(`- TLC: ${tlcOk}/${tlcTotal} ok`);
lines.push(`- Alloy: ${alloyOk}/${alloyTotal} ok`);
lines.push(tlaSum ? `- TLA summary file: ${path.basename(tlaSum)}` : "- TLA summary: n/a");
lines.push(alloySum ? `- Alloy summary file: ${path.basename(alloySum)}` : "- Alloy summary: n/a");
if (alloyS && alloyS.temporal) {
  const t = alloyS.temporal;
  const ops = Array.isArray(t.operators) && t.operators.length ? ` (ops: ${t.operators.join(', ')})` : '';
  lines.push(`- Alloy temporal: ${t.present ? 'present' : 'absent'}${ops}`);
}
lines.push(smtSum ? `- SMT summary file: ${path.basename(smtSum)}` : "- SMT summary: n/a");
if (smt) {
  const ss = [
    `solver=${smt.solver || 'n/a'}`,
    `status=${smt.status || 'n/a'}`
  ].join(' ');
  lines.push(`- SMT: ${ss}`);
}
lines.push(kaniSum ? `- Kani summary file: ${path.basename(kaniSum)}` : "- Kani summary: n/a");
if (kani) {
  const ks = [
    `status=${kani.status || 'n/a'}`,
    `detected=${kani.detected ? 'yes' : 'no'}`
  ].join(' ');
  lines.push(`- Kani: ${ks}`);
}
lines.push(spinSum ? `- SPIN summary file: ${path.basename(spinSum)}` : "- SPIN summary: n/a");
if (spin) {
  lines.push(`- SPIN: status=${spin.status || 'n/a'}${spin.ltl ? ` ltl=${spin.ltl}` : ''}`);
}
lines.push(cspSum ? `- CSP summary file: ${path.basename(cspSum)}` : "- CSP summary: n/a");
if (csp) {
  const backend = csp.backend ? ` backend=${csp.backend}` : '';
  const resultStatus = csp.resultStatus ? ` result=${csp.resultStatus}` : '';
  const exitCode = (typeof csp.exitCode === 'number') ? ` exitCode=${csp.exitCode}` : '';
  lines.push(`- CSP: status=${csp.status || 'n/a'}${backend}${resultStatus}${exitCode}`);
}
lines.push(leanSum ? `- Lean summary file: ${path.basename(leanSum)}` : "- Lean summary: n/a");
if (lean) {
  lines.push(`- Lean: status=${lean.status || 'n/a'}`);
}
if (conf && conf.runtimeHooks) {
  const h = conf.runtimeHooks;
  const info = `present=${h.present? 'yes':'no'} count=${h.count||0} traceId=${h.traceId||'n/a'} match=${h.matchesReplayTraceId? 'yes':'no'}`;
  lines.push(`- Runtime hooks: ${info}`);
}
// Present map (single source for MD + JSON)
const present = {
  tla: !!tlaSum,
  alloy: !!alloySum,
  smt: !!smtSum,
  apalache: !!apalacheSum,
  conformance: !!confSum,
  kani: !!kaniSum,
  spin: !!spinSum,
  csp: !!cspSum,
  lean: !!leanSum
};
// Quick one-line present/ran summary（MD表示とJSONのpresentを完全同期）
const order = ['tla','alloy','smt','apalache','conformance','kani','spin','csp','lean'];
const presentKeys = order.filter(k => present[k]);
const presentCount = presentKeys.length;
const presentTotal = order.length;
lines.push('### Presence');
lines.push(`Present: ${presentCount}/${presentTotal}${presentCount? ` (${presentKeys.join(', ')})` : ''}`);
// Alloy temporal operator presence (if summary includes it)
try {
  const t = alloyS && alloyS.temporal;
  if (t && (t.present || (Array.isArray(t.operators) && t.operators.length))) {
    const ops = Array.isArray(t.operators) ? t.operators.join(', ') : '';
    const pops = Array.isArray(t.pastOperators) ? t.pastOperators.join(', ') : '';
    lines.push(`Alloy temporal: present=${!!t.present}${ops? ` ops=[${ops}]`:''}${pops? ` past=[${pops}]`:''}`);
  }
} catch {}
// Apalache ran/ok line（MDとJSONの両方で一貫表記）
lines.push(`Apalache ran/ok: ${apalacheSum && apalache ? (apalache.ran? 'yes':'no') : 'n/a'}/${apalacheSum && apalache ? (apalache.ok==null? 'n/a' : (apalache.ok? 'yes':'no')) : 'n/a'}`);
lines.push("");
// Visual separation for presence block
lines.push("\n---");

if (apalacheSum && apalache) {
  const v = apalache.version || 'n/a';
  const ok = apalache.ok; // may be boolean or null
  const ran = apalache.ran;
  const status = apalache.status;
  const timeMs = apalache.timeMs || null;
  const toolPath = apalache.toolPath || '';
  const run = apalache.run || '';
  const ec = (typeof apalache.errorCount === 'number') ? apalache.errorCount : null;
  lines.push(`- Apalache: ran=${ran? 'yes':'no'} ok=${ok==null? 'n/a': (ok? 'yes':'no')} status=${status||'n/a'}${ec!=null?`, errors=${ec}`:''} (v=${v}${timeMs?`, ${Math.round(timeMs/1000)}s`:''})`);
  const hints=[];
  if (toolPath) hints.push(`tool: ${toolPath}`);
  if (run) hints.push(`run: ${run}`);
  if (apalacheOut) hints.push(`output: ${path.basename(apalacheOut)}`);
  if (hints.length) lines.push('  - ' + hints.join(' | '));
  if (ok === false && Array.isArray(apalache.errors) && apalache.errors.length > 0) {
    lines.push('');
    lines.push('<details><summary>Apalache errors (top)</summary>');
    lines.push('');
    lines.push('```text');
    for (const e of apalache.errors.slice(0,ERRORS_LIMIT)) lines.push(escMd(clamp(e)));
    lines.push('```');
    lines.push('');
    lines.push('</details>');
  }
  if (ok === false && apalache.errorSnippet && Array.isArray(apalache.errorSnippet.lines)) {
    const MAX_LINES = parseInt(process.env.FORMAL_AGG_SNIPPET_MAX_LINES || '20', 10);
    const ctxAll = apalache.errorSnippet.lines.map(l => escMd(clamp(l))).filter(l => String(l).trim().length>0);
    const ctxLines = ctxAll.slice(0, Math.max(0, MAX_LINES));
    if (ctxLines.length) {
      lines.push('');
      lines.push('- First error context:');
      lines.push('');
      lines.push('```text');
      for (const l of ctxLines) lines.push(l);
      lines.push('```');
    }
  }
} else {
  lines.push("- Apalache summary: n/a");
}
lines.push(confSum ? `- Conformance summary file: ${path.basename(confSum)}` : "- Conformance summary: n/a");
// By-type/present summary（簡潔・Present行の補助、一行で整形）
// Deterministic by-type present line (JSON→MDと順序を完全同期)
const presentList = order.filter(k => present[k]);
lines.push('### Aggregate Status');
lines.push(`- By-type present: ${presentList.length}/${presentTotal}${presentList.length? ` (${presentList.join(', ')})` : ''}`);
if (apalacheSum && apalache) {
  lines.push(`- Apalache ran/ok: ran=${apalache.ran? 'yes':'no'} ok=${apalache.ok==null? 'n/a': (apalache.ok? 'yes':'no')}`);
}
lines.push('');
// Footer meta（順序を統一: Tools → Reproduce → Policy → Clamp → Generated）
lines.push('---');
lines.push("_Tools check: pnpm run tools:formal:check_");
lines.push("_Reproduce locally: pnpm run verify:tla -- --engine=apalache_ (see docs/quality/formal-runbook.md)");
lines.push("_Non-blocking. Add/remove label run-formal to control._");
lines.push(`_Clamp: line=${clampInfo.lineClamp}, errors=${clampInfo.errorsLimit}_`);
lines.push(`_Generated: ${GENERATED_AT}_`);
// Normalize markdown: collapse excessive empty lines + optional long-line wrap (outside code fences)
function normalizeMd(arr){
  const out=[]; let prevEmpty=false; let inFence=false;
  const wrapWidth = parseInt(process.env.FORMAL_AGG_WRAP_WIDTH || '0', 10); // 0=disable
  for (let raw of arr){
    let l = String(raw).replace(/\s+$/,''); // trim trailing spaces
    if (l.startsWith('```')) inFence = !inFence; // toggle on code fences
    if (!inFence && wrapWidth > 0 && l.length > wrapWidth){
      // wrap at spaces without breaking words
      const wrapped = [];
      let s = l;
      while (s.length > wrapWidth){
        let cut = s.lastIndexOf(' ', wrapWidth);
        if (cut < 0) cut = wrapWidth;
        wrapped.push(s.slice(0, cut));
        s = s.slice(cut).replace(/^\s+/, '');
      }
      if (s.length) wrapped.push(s);
      l = wrapped.join('\n');
    }
    const isEmpty = l.trim().length===0;
    if (isEmpty && prevEmpty) continue; // collapse multiple blanks
    out.push(l);
    prevEmpty = isEmpty;
  }
  const joined = out.join("\n");
  return joined
    .replace(/\n{3,}/g, "\n\n")
    .replace(/\n+$/, "\n");
}
// JSON aggregate for tooling（single source of truth for present/by-type）
const json = {
  tlc: { ok: tlcOk, total: tlcTotal },
  alloy: { ok: alloyOk, total: alloyTotal, summary: alloyS || null },
  tla: tla || null,
  smt: smt || null,
  apalache: apalache || null,
  conformance: conf || null,
  kani: kani || null,
  spin: spin || null,
  csp: csp || null,
  lean: lean || null,
  info: { 
    lineClamp: LINE_CLAMP, 
    errorsLimit: ERRORS_LIMIT, 
    generatedAt: GENERATED_AT, 
    present, 
    presentCount,
    presentTotal,
    presentOrder: order,
    ranOk: {
      apalache: apalache ? { ran: !!apalache.ran, ok: (typeof apalache.ok === 'boolean' ? apalache.ok : null) } : null
    },
    temporal: {
      alloy: alloyS && alloyS.temporal ? alloyS.temporal : null
    }
  }
};
// Append an explicit consistency line referencing JSON info.present
lines.push(`Consistency: MD=JSON present (${presentCount}/${presentTotal})`);
lines.push('_Source: info.present (aggregate JSON)_');
const md = normalizeMd(lines);
fs.writeFileSync(outMd, md);
fs.writeFileSync(outJson, JSON.stringify(json,null,2));
const aggPresent = fs.existsSync(outJson) ? 'yes' : 'no';
console.log(md + "\nArtifacts: aggregate-json=" + aggPresent);
