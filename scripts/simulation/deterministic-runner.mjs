#!/usr/bin/env node
// Deterministic simulation harness (stub): produces a summary with a fixed seed
import fs from 'node:fs';
import path from 'node:path';

const seed = Number(process.env.SIM_SEED || 42);
function prng(s){ return () => (s = Math.imul(48271, s) % 0x7fffffff) / 0x7fffffff; }
const rand = prng(seed);
const steps = Number(process.env.SIM_STEPS || 10);
const outFile = 'artifacts/simulation/deterministic-summary.json';
fs.mkdirSync(path.dirname(outFile), { recursive: true });

const results = [];
for (let i=0;i<steps;i++){
  results.push({ step: i+1, value: Math.floor(rand()*1000) });
}

const summary = {
  ok: true,
  seed,
  steps,
  values: results.map(r=>r.value),
  timestamp: new Date().toISOString()
};

fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`✓ Deterministic simulation summary written: ${outFile}`);
process.exit(0);

