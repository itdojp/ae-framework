import fs from 'node:fs';
import path from 'node:path';

function readJsonSafe(p){
  try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; }
}

function find(base, rel){
  const p = path.join(base, rel);
  return fs.existsSync(p) ? p : undefined;
}

export function computeAggregateInfo(baseDir){
  const tlaSum = find(baseDir, 'formal-reports-tla/tla-summary.json');
  const alloySum = find(baseDir, 'formal-reports-alloy/alloy-summary.json');
  const smtSum = find(baseDir, 'formal-reports-smt/smt-summary.json');
  const apalacheSum = find(baseDir, 'formal-reports-apalache/apalache-summary.json');
  const confSum = find(baseDir, 'formal-reports-conformance/conformance-summary.json');

  const apalache = apalacheSum ? readJsonSafe(apalacheSum) : undefined;

  const present = {
    tla: !!tlaSum,
    alloy: !!alloySum,
    smt: !!smtSum,
    apalache: !!apalacheSum,
    conformance: !!confSum,
  };
  const presentCount = Object.values(present).filter(Boolean).length;
  const ranOk = {
    apalache: apalache ? { ran: !!apalache.ran, ok: (typeof apalache.ok === 'boolean' ? apalache.ok : null) } : null
  };
  return { present, presentCount, ranOk };
}

// Deterministic表示用のキー順（tla→alloy→smt→apalache→conformance）
export const ORDERED_PRESENT_KEYS = ['tla', 'alloy', 'smt', 'apalache', 'conformance'];

// present（{k: boolean}）から、true のものを ORDERED_PRESENT_KEYS 順に並べて返す
export function orderedPresentPairs(present){
  if (!present) return [];
  return ORDERED_PRESENT_KEYS
    .filter((k) => present[k])
    .map((k) => [k, true]);
}

// MD向けの一行表現を組み立て（空なら空文字）。呼び出し側で前置語を付ける想定でも可
export function formatByTypePresentLine(info){
  const p = info?.present || {};
  const pairs = orderedPresentPairs(p);
  const count = pairs.length;
  if (count === 0) return 'By-type present: 0/5';
  const names = pairs.map(([k]) => k).join(', ');
  return `By-type present: ${count}/5 (${names})`;
}
