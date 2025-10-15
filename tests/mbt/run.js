#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

// Deterministic PRNG for reproducible MBT runs.
// See: https://github.com/bryc/code/blob/master/jshash/PRNGs.md
const MULBERRY32_INCREMENT = 0x6D2B79F5;
const MULBERRY32_MIX_CONSTANT = 61;

// Lightweight 32-bit PRNG returning deterministic values in [0, 1).
function mulberry32(seed) {
  let t = seed >>> 0;
  return () => {
    t += MULBERRY32_INCREMENT;
    let r = Math.imul(t ^ (t >>> 15), t | 1);
    r ^= r + Math.imul(r ^ (r >>> 7), r | MULBERRY32_MIX_CONSTANT);
    return ((r ^ (r >>> 14)) >>> 0) / 4294967296;
  };
}

function parseArgs(argv) {
  const out = { runs: 25, depth: 12 };
  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg.startsWith('--seed=')) out.seed = Number(arg.slice(7));
    else if (arg.startsWith('--runs=')) out.runs = Number(arg.slice(7));
    else if (arg.startsWith('--depth=')) out.depth = Number(arg.slice(8));
  }
  return out;
}

function pickTransition(rand, transitions) {
  const idx = Math.floor(rand() * transitions.length);
  return transitions[idx];
}

function createModel() {
  return {
    available: 5,
    reserved: 0,
    shipped: 0,
    history: [],
  };
}

function applyTransition(model, transition) {
  if (!transition.guard(model)) {
    return { applied: false, reason: transition.name + ' guard failed' };
  }
  transition.effect(model);
  model.history.push(transition.name);
  return { applied: true };
}

function evaluateInvariants(model, initialTotal) {
  const violations = [];
  if (model.available < 0) {
    violations.push('available went negative');
  }
  if (model.reserved < 0) {
    violations.push('reserved went negative');
  }
  if (model.available + model.reserved + model.shipped !== initialTotal) {
    violations.push('inventory conservation violated');
  }
  return violations;
}

function runScenario(rand, depth) {
  const initialTotal = 5;
  const model = createModel();
  const transitions = [
    {
      name: 'reserve',
      guard: (m) => m.available > 0,
      effect: (m) => {
        m.available -= 1;
        m.reserved += 1;
      },
    },
    {
      name: 'cancel',
      guard: (m) => m.reserved > 0,
      effect: (m) => {
        m.available += 1;
        m.reserved -= 1;
      },
    },
    {
      name: 'ship',
      guard: (m) => m.reserved > 0,
      effect: (m) => {
        m.reserved -= 1;
        m.shipped += 1;
      },
    },
  ];

  const steps = [];
  for (let i = 0; i < depth; i += 1) {
    const transition = pickTransition(rand, transitions);
    const { applied, reason } = applyTransition(model, transition);
    steps.push({ action: transition.name, applied, reason: reason || null });
  }

  const violations = evaluateInvariants(model, initialTotal);
  return { steps, finalState: model, violations };
}

function ensureOutputDir(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

async function main() {
  const opts = parseArgs(process.argv);
  const seed = Number.isFinite(opts.seed) ? opts.seed : Date.now();
  const rand = mulberry32(seed);
  const summary = {
    seed,
    runs: opts.runs,
    depth: opts.depth,
    scenarios: [],
    violations: 0,
  };

  for (let i = 0; i < opts.runs; i += 1) {
    const scenario = runScenario(rand, opts.depth);
    summary.scenarios.push({
      index: i + 1,
      steps: scenario.steps,
      final: {
        available: scenario.finalState.available,
        reserved: scenario.finalState.reserved,
        shipped: scenario.finalState.shipped,
      },
      violations: scenario.violations,
    });
    summary.violations += scenario.violations.length;
  }

  const outputPath = 'artifacts/mbt/summary.json';
  ensureOutputDir(outputPath);
  fs.writeFileSync(outputPath, JSON.stringify(summary, null, 2));
  console.log(`✓ MBT harness wrote ${outputPath} (seed=${seed}, runs=${summary.runs}, violations=${summary.violations})`);

  if (summary.violations > 0) {
    console.error('MBT invariants violated. Inspect artifacts/mbt/summary.json for details.');
    process.exitCode = 1;
  }
}

main().catch((err) => {
  console.error('[mbt] unexpected error:', err);
  process.exit(1);
});
