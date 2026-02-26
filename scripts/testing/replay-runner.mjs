#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

function readJson(filePath) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf-8'));
  } catch {
    return undefined;
  }
}

function writeJson(filePath, payload) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`);
}

function toIntegerOrUndefined(rawValue) {
  if (rawValue === undefined || rawValue === null || rawValue === '') {
    return undefined;
  }
  const value = Number.parseInt(String(rawValue), 10);
  return Number.isFinite(value) ? value : undefined;
}

function parseArgs(argv) {
  const out = {};
  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg.startsWith('--focus=')) out.focus = arg.slice(8);
    else if (arg.startsWith('--seed=')) out.seed = toIntegerOrUndefined(arg.slice(7));
    else if (arg.startsWith('--input=')) out.input = arg.slice(8);
    else if (arg.startsWith('--output=')) out.output = arg.slice(9);
  }
  return out;
}

function applyEvent(state, event) {
  const qty = event?.payload?.qty ?? 0;
  switch (event?.name) {
    case 'ItemReceived':
      state.onHand = (state.onHand ?? 0) + qty;
      break;
    case 'ItemAllocated':
      state.allocated = (state.allocated ?? 0) + qty;
      break;
    case 'ItemShipped':
      state.onHand = (state.onHand ?? 0) - qty;
      state.allocated = Math.max((state.allocated ?? 0) - qty, 0);
      break;
    default:
      break;
  }
}

function checkInvariants(state) {
  const violations = [];
  const disable = new Set((process.env.REPLAY_DISABLE || '').split(',').map((value) => value.trim()).filter(Boolean));
  const only = new Set((process.env.REPLAY_ONLY || '').split(',').map((value) => value.trim()).filter(Boolean));
  const onHandMin = Number.isFinite(Number(process.env.REPLAY_ONHAND_MIN)) ? Number(process.env.REPLAY_ONHAND_MIN) : 0;

  const enabled = (name) => (only.size > 0 ? only.has(name) : !disable.has(name));

  if (enabled('allocated_le_onhand') && (state.allocated ?? 0) > (state.onHand ?? 0)) {
    violations.push('allocated <= onHand');
  }
  if (enabled('onhand_min') && (state.onHand ?? 0) < onHandMin) {
    violations.push(`onHand >= ${onHandMin}`);
  }

  return violations;
}

function buildReproCommand({ inputPath, outputPath, focus, seed }) {
  const parts = [
    `REPLAY_INPUT=${inputPath}`,
    `REPLAY_OUTPUT=${outputPath}`,
    `REPLAY_SEED=${seed}`,
    'REPLAY_STRICT=1',
    'node scripts/testing/replay-runner.mjs',
  ];
  if (focus) {
    parts.push(`--focus=${focus}`);
  }
  return parts.join(' ');
}

function sanitizeFileToken(value) {
  return String(value).replace(/[^a-zA-Z0-9._-]+/g, '-');
}

async function main() {
  const startedAt = Date.now();
  const args = parseArgs(process.argv);
  const focus = args.focus;
  const inputPath = args.input ?? process.env.REPLAY_INPUT ?? 'artifacts/domain/events.json';
  const outputPath = args.output ?? process.env.REPLAY_OUTPUT ?? 'artifacts/domain/replay.summary.json';
  const strict = (process.env.REPLAY_STRICT ?? '1') !== '0';
  const seed = args.seed ?? toIntegerOrUndefined(process.env.REPLAY_SEED) ?? 0;

  const events = readJson(inputPath) || [];
  const state = { onHand: 0, allocated: 0 };
  for (const event of events) {
    applyEvent(state, event);
  }

  const violations = checkInvariants(state);
  const ok = violations.length === 0;
  const traceId = (Array.isArray(events) && events[0]?.traceId)
    ? events[0].traceId
    : (focus || `replay-${seed}`);
  const durationMs = Math.max(0, Date.now() - startedAt);
  const summary = {
    traceId,
    seed,
    runs: 1,
    passed: ok ? 1 : 0,
    failed: ok ? 0 : 1,
    durationMs,
    reproducibleCommand: buildReproCommand({ inputPath, outputPath, focus, seed }),
    totalEvents: events.length,
    finalState: state,
    violatedInvariants: violations,
    generatedAtUtc: new Date().toISOString(),
  };

  if (!ok) {
    const token = sanitizeFileToken(traceId || 'unknown');
    const counterexamplePath = process.env.REPLAY_COUNTEREXAMPLE_PATH || `artifacts/replay/counterexample-${token}.json`;
    writeJson(counterexamplePath, {
      traceId,
      seed,
      events,
      finalState: state,
      violatedInvariants: violations,
      reproducibleCommand: summary.reproducibleCommand,
      generatedAtUtc: summary.generatedAtUtc,
    });
    summary.counterexamplePath = counterexamplePath;
  }

  writeJson(outputPath, summary);
  if (process.env.REPLAY_PRINT_SUMMARY === '1') {
    console.log('summary:', JSON.stringify(summary, null, 2));
  }
  console.log(`${ok ? 'ok' : 'fail'} replay checked events=${events.length} violations=${violations.length} output=${outputPath}`);
  process.exit(strict ? (ok ? 0 : 1) : 0);
}

main().catch((error) => {
  console.error('replay-runner error:', error);
  process.exit(1);
});
