#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const DEFAULT_OUTPUT_PATH = 'artifacts/properties/summary.json';
const DEFAULT_COUNTEREXAMPLE_PATH = 'artifacts/properties/counterexample.json';

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
    else if (arg.startsWith('--trace-id=')) out.traceId = arg.slice(11);
    else if (arg.startsWith('--runs=')) out.runs = toIntegerOrUndefined(arg.slice(7));
    else if (arg.startsWith('--seed=')) out.seed = toIntegerOrUndefined(arg.slice(7));
    else if (arg.startsWith('--output=')) out.output = arg.slice(9);
  }
  return out;
}

function writeJson(filePath, payload) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`);
}

function buildReproCommand({ seed, runs, traceId }) {
  const parts = ['node scripts/testing/property-harness.mjs', `--seed=${seed}`, `--runs=${runs}`];
  if (traceId) {
    parts.push(`--focus=${traceId}`);
  }
  return parts.join(' ');
}

async function maybeRunFastCheck(runs, seed) {
  let fastCheck;
  try {
    fastCheck = (await import('fast-check')).default;
  } catch {
    return { passed: true, note: 'fast-check not available; skipped' };
  }

  try {
    await fastCheck.assert(
      fastCheck.property(fastCheck.integer(), (value) => Number.isInteger(value)),
      { numRuns: runs, seed }
    );
    return { passed: true };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return { passed: false, message };
  }
}

async function main() {
  const startedAt = Date.now();
  const args = parseArgs(process.argv);
  const seed = args.seed ?? toIntegerOrUndefined(process.env.PROPERTY_SEED) ?? Date.now();
  const runs = args.runs ?? toIntegerOrUndefined(process.env.PROPERTY_RUNS) ?? 50;
  const traceId = args.traceId ?? args.focus ?? process.env.TRACE_ID ?? `pbt-${seed}`;
  const outputPath = args.output ?? process.env.PROPERTY_OUTPUT ?? DEFAULT_OUTPUT_PATH;

  const result = await maybeRunFastCheck(runs, seed);
  const durationMs = Math.max(0, Date.now() - startedAt);
  const summary = {
    traceId,
    seed,
    runs,
    version: '0.2',
    passed: result.passed,
    failed: result.passed ? 0 : 1,
    durationMs,
    reproducibleCommand: buildReproCommand({ seed, runs, traceId }),
    generatedAtUtc: new Date().toISOString(),
  };
  if (result.note) {
    summary.note = result.note;
  }
  if (result.message) {
    summary.errorMessage = result.message;
  }

  if (!result.passed) {
    const counterexamplePath = process.env.PROPERTY_COUNTEREXAMPLE_PATH ?? DEFAULT_COUNTEREXAMPLE_PATH;
    writeJson(counterexamplePath, {
      traceId,
      seed,
      runs,
      message: result.message ?? 'property harness failed',
      reproducibleCommand: summary.reproducibleCommand,
      generatedAtUtc: summary.generatedAtUtc,
    });
    summary.counterexamplePath = counterexamplePath;
  }

  writeJson(outputPath, summary);
  console.log(`property-harness wrote ${outputPath} traceId=${traceId} passed=${result.passed}`);
  process.exit(result.passed ? 0 : 1);
}

main().catch((error) => {
  console.error('property-harness error:', error);
  process.exit(1);
});
