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

