#!/usr/bin/env node
/**
 * Minimal model evaluation runner for AE-IR aiModels.
 *
 * Usage:
 *   tsx scripts/model-eval/run.ts --input <dataset.json> [--aeir <ae-ir.json> --model <name>] \
 *     [--threshold key=expr] [--prohibited term1,term2] [--output <path>]
 *
 * Exit codes:
 *   0 - All checks pass.
 *   1 - Evaluation failed (thresholds not met / prohibited content detected).
 *   2 - Configuration or operational error (invalid flags, unreadable files, malformed input).
 *
 * Thresholds:
 *   - aiModel.metrics from --aeir are merged with --threshold CLI flags.
 *   - CLI --threshold overrides take precedence on key conflicts.
 *   - If a threshold is defined but its metric is unavailable, the gate fails with metric_unavailable.
 *
 * Prohibited terms:
 *   - Merged from dataset.prohibited, aiModel.safety.prohibitedOutputs, and --prohibited flag.
 *
 * Dataset JSON format:
 *   - Either an array of cases, or an object with { cases: CaseRow[], prohibited?: string[] }.
 */
import fs from 'node:fs';
import path from 'node:path';
import { compare } from '../../src/utils/comparator.js';
import { toMessage } from '../../src/utils/error-utils.js';

type Thresholds = Record<string, string>;

type CaseRow = {
  expected?: unknown;
  actual?: unknown;
  predicted?: unknown;
  output?: unknown;
  outputText?: unknown;
  latencyMs?: unknown;
};

type Dataset = {
  cases?: CaseRow[];
  prohibited?: string[];
};

type AiModelSpec = {
  name: string;
  provider?: string;
  metrics?: Record<string, string>;
  safety?: { prohibitedOutputs?: string[] };
};

const stableStringify = (value: unknown): string => {
  const seen = new WeakSet<object>();
  const replacer = (_key: string, val: unknown) => {
    if (val && typeof val === 'object') {
      const obj = val as object;
      if (seen.has(obj)) {
        return '[Circular]';
      }
      seen.add(obj);
      if (Array.isArray(obj)) {
        return obj;
      }
      const sorted: Record<string, unknown> = {};
      Object.keys(obj as Record<string, unknown>).sort().forEach((key) => {
        sorted[key] = (obj as Record<string, unknown>)[key];
      });
      return sorted;
    }
    return val;
  };
  return JSON.stringify(value, replacer);
};

const toComparable = (value: unknown): string => {
  if (value === null || value === undefined) return String(value);
  if (typeof value === 'string' || typeof value === 'number' || typeof value === 'boolean') {
    return String(value);
  }
  try {
    return stableStringify(value);
  } catch {
    return String(value);
  }
};

const isEquivalent = (left: unknown, right: unknown): boolean => toComparable(left) === toComparable(right);

const args = process.argv.slice(2);

const getArg = (name: string): string | undefined => {
  const idx = args.indexOf(name);
  if (idx === -1) return undefined;
  const value = args[idx + 1];
  if (!value || value.startsWith('-')) return undefined;
  return value;
};

const getArgs = (name: string): string[] => {
  const values: string[] = [];
  for (let i = 0; i < args.length; i += 1) {
    if (args[i] === name && args[i + 1]) {
      values.push(args[i + 1]);
    }
    if (args[i].startsWith(`${name}=`)) {
      const eqIndex = args[i].indexOf('=');
      values.push(eqIndex >= 0 ? args[i].slice(eqIndex + 1) : '');
    }
  }
  return values.filter(Boolean);
};

const inputPath = getArg('--input') ?? getArg('-i');
const aeirPath = getArg('--aeir') ?? getArg('--ir');
const modelName = getArg('--model');
const outputPath = getArg('--output') ?? 'artifacts/model-eval/summary.json';
const prohibitedCsv = getArg('--prohibited');

if (!inputPath) {
  console.error('model-eval: --input is required');
  process.exit(2);
}

const readJson = <T>(p: string): T => {
  const raw = fs.readFileSync(p, 'utf8');
  return JSON.parse(raw) as T;
};

const thresholds: Thresholds = {};
for (const entry of getArgs('--threshold')) {
  const eqIndex = entry.indexOf('=');
  const key = eqIndex >= 0 ? entry.slice(0, eqIndex) : '';
  const expr = eqIndex >= 0 ? entry.slice(eqIndex + 1) : '';
  if (!key || !expr) {
    console.error(`model-eval: invalid --threshold ${entry} (use key=expr)`);
    process.exit(2);
  }
  thresholds[key.trim()] = expr.trim();
}

let aiModel: AiModelSpec | undefined;
if (aeirPath && modelName) {
  try {
    const aeir = readJson<{ aiModels?: AiModelSpec[] }>(aeirPath);
    aiModel = aeir.aiModels?.find((m) => m.name === modelName);
    if (!aiModel) {
      console.error(`model-eval: aiModels entry not found for name=${modelName}`);
      process.exit(2);
    }
  } catch (error) {
    console.error(`model-eval: failed to load AE-IR: ${toMessage(error)}`);
    process.exit(2);
  }
}

let datasetRaw: Dataset | CaseRow[];
try {
  datasetRaw = readJson<Dataset | CaseRow[]>(inputPath);
} catch (error) {
  console.error(`model-eval: failed to load dataset: ${toMessage(error)}`);
  process.exit(2);
}
const cases: CaseRow[] = Array.isArray(datasetRaw) ? datasetRaw : (datasetRaw.cases ?? []);
if (cases.length === 0) {
  console.error('model-eval: dataset contains no cases to evaluate');
  process.exit(2);
}

const prohibitedTerms: string[] = [];
if (prohibitedCsv) {
  prohibitedTerms.push(...prohibitedCsv.split(',').map((t) => t.trim()).filter(Boolean));
}
const datasetProhibited = (datasetRaw as Dataset).prohibited;
if (Array.isArray(datasetProhibited)) {
  prohibitedTerms.push(...datasetProhibited.map((t) => t.trim()).filter(Boolean));
}
const modelProhibited = aiModel?.safety?.prohibitedOutputs ?? [];
prohibitedTerms.push(...modelProhibited.map((t) => t.trim()).filter(Boolean));

const uniqueProhibited = Array.from(new Set(prohibitedTerms)).filter(Boolean);
const uniqueProhibitedLower = uniqueProhibited.map((term) => term.toLowerCase());

const takeValue = (row: CaseRow, keys: Array<keyof CaseRow>): unknown => {
  for (const key of keys) {
    const value = row[key];
    if (value !== undefined && value !== null) return value;
  }
  return undefined;
};

let correct = 0;
let totalForAccuracy = 0;
let totalLatency = 0;
let latencySamples = 0;
let prohibitedHits = 0;
let outputsChecked = 0;

cases.forEach((row) => {
  const expected = takeValue(row, ['expected']);
  const actual = takeValue(row, ['actual', 'predicted', 'output']);
  if (expected !== undefined && actual !== undefined) {
    totalForAccuracy += 1;
    if (isEquivalent(actual, expected)) {
      correct += 1;
    }
  }

  const latencyRaw = row.latencyMs;
  if (typeof latencyRaw === 'number' && Number.isFinite(latencyRaw)) {
    latencySamples += 1;
    totalLatency += latencyRaw;
  }

  const outputText = takeValue(row, ['outputText', 'output', 'actual', 'predicted']);
  if (typeof outputText === 'string' && uniqueProhibitedLower.length > 0) {
    outputsChecked += 1;
    const lower = outputText.toLowerCase();
    if (uniqueProhibitedLower.some((term) => lower.includes(term))) {
      prohibitedHits += 1;
    }
  }
});

const accuracy = totalForAccuracy > 0 ? correct / totalForAccuracy : null;
const latencyMs = latencySamples > 0 ? totalLatency / latencySamples : null;
const prohibitedRate = outputsChecked > 0 ? prohibitedHits / outputsChecked : null;

const metrics: Record<string, number | null> = {
  accuracy,
  latencyMs,
  prohibitedRate,
};

const mergedThresholds: Thresholds = {
  ...(aiModel?.metrics ?? {}),
  ...thresholds,
};

const evaluations: Record<string, { value: number | null; threshold: string; passed: boolean; reason?: string }> = {};
let failed = 0;

for (const [key, expr] of Object.entries(mergedThresholds)) {
  const value = metrics[key];
  if (value === null || value === undefined) {
    evaluations[key] = { value: null, threshold: expr, passed: false, reason: 'metric_unavailable' };
    failed += 1;
    continue;
  }
  let passed = false;
  try {
    passed = compare(value, expr);
  } catch (error) {
    evaluations[key] = { value, threshold: expr, passed: false, reason: toMessage(error) };
    failed += 1;
    continue;
  }
  evaluations[key] = { value, threshold: expr, passed };
  if (!passed) failed += 1;
}

const summary = {
  generatedAt: new Date().toISOString(),
  model: aiModel ? { name: aiModel.name, provider: aiModel.provider ?? null } : null,
  dataset: {
    totalCases: cases.length,
    accuracySamples: totalForAccuracy,
    latencySamples,
    outputsChecked,
    prohibitedTerms: uniqueProhibited,
  },
  metrics,
  thresholds: mergedThresholds,
  evaluations,
  passed: failed === 0,
};

try {
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, JSON.stringify(summary, null, 2));
  console.log(`✓ Wrote ${outputPath}`);
} catch (error) {
  console.error(`model-eval: failed to write output (${outputPath}): ${toMessage(error)}`);
  process.exit(2);
}

process.exitCode = failed === 0 ? 0 : 1;
