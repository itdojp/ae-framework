#!/usr/bin/env node
// Aggregate formal reports into artifacts/hermetic-reports/formal/summary.json
import fs from 'node:fs';
import path from 'node:path';

const repoRoot = process.cwd();
const formalDir = path.join(repoRoot, 'artifacts/hermetic-reports', 'formal');
const confDir = path.join(repoRoot, 'artifacts/hermetic-reports', 'conformance');
fs.mkdirSync(formalDir, { recursive: true });

function readJsonSafe(p){ try { return JSON.parse(fs.readFileSync(p,'utf8')); } catch { return undefined; } }

const conformance = readJsonSafe(path.join(confDir, 'summary.json'));
const smt = readJsonSafe(path.join(formalDir, 'smt-summary.json'));
const alloy = readJsonSafe(path.join(formalDir, 'alloy-summary.json'));
const tla = readJsonSafe(path.join(formalDir, 'tla-summary.json'));
const apalache = readJsonSafe(path.join(formalDir, 'apalache-summary.json'));
const kani = readJsonSafe(path.join(formalDir, 'kani-summary.json'));
const spin = readJsonSafe(path.join(formalDir, 'spin-summary.json'));
const csp = readJsonSafe(path.join(formalDir, 'csp-summary.json'));
const lean = readJsonSafe(path.join(formalDir, 'lean-summary.json'));

const summary = {
  timestamp: new Date().toISOString(),
  present: {
    conformance: !!conformance,
    smt: !!smt,
    alloy: !!alloy,
    tla: !!tla,
    apalache: !!apalache,
    kani: !!kani,
    spin: !!spin,
    csp: !!csp,
    lean: !!lean
  },
  conformance: conformance || null,
  smt: smt || null,
  alloy: alloy || null,
  tla: tla || null,
  apalache: apalache || null,
  kani: kani || null,
  spin: spin || null,
  csp: csp || null,
  lean: lean || null
};

const outFile = path.join(formalDir, 'summary.json');
fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`Formal summary written: ${path.relative(repoRoot, outFile)}`);
process.exit(0);
