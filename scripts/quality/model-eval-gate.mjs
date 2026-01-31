#!/usr/bin/env node
/**
 * Quality gate wrapper for model evaluation.
 * Resolves dataset/model from AE-IR or environment variables and runs model:eval.
 */

import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

const cwd = process.cwd();
const aeirPath = process.env.AE_MODEL_EVAL_AEIR || '.ae/ae-ir.json';
const modelFilter = process.env.AE_MODEL_EVAL_MODEL;
const inputOverride = process.env.AE_MODEL_EVAL_INPUT;
const thresholdOverrides = (process.env.AE_MODEL_EVAL_THRESHOLD || '')
  .split(',')
  .map((value) => value.trim())
  .filter(Boolean);

function fileExists(filePath) {
  try {
    return fs.existsSync(filePath);
  } catch {
    return false;
  }
}

function readJson(filePath) {
  const raw = fs.readFileSync(filePath, 'utf8');
  return JSON.parse(raw);
}

function sanitizeName(value) {
  return value.replace(/[^a-zA-Z0-9_.-]/g, '-');
}

let aeirLoadFailed = false;

function resolveAeir() {
  if (!fileExists(aeirPath)) {
    return null;
  }
  try {
    return readJson(aeirPath);
  } catch (error) {
    console.error(`[model-eval-gate] Failed to parse AE-IR: ${String(error)}`);
    aeirLoadFailed = true;
    return null;
  }
}

const aeir = resolveAeir();
const aiModels = Array.isArray(aeir?.aiModels) ? aeir.aiModels : [];

function selectModels() {
  if (!aiModels.length) {
    return [];
  }
  if (!modelFilter) {
    return aiModels;
  }
  const selected = aiModels.filter((model) => model?.name === modelFilter);
  if (!selected.length) {
    console.error(`[model-eval-gate] aiModels entry not found for name=${modelFilter}`);
    process.exit(2);
  }
  return selected;
}

const selectedModels = selectModels();

function resolveDataset(model) {
  if (inputOverride) {
    return inputOverride;
  }
  return model?.evaluation?.dataset || null;
}

if (!inputOverride && aeirLoadFailed) {
  console.error('[model-eval-gate] AE-IR exists but could not be parsed; aborting model evaluation.');
  process.exit(2);
}

if (!inputOverride && !selectedModels.length) {
  console.log('[model-eval-gate] Skipping model evaluation (no AE-IR aiModels and no dataset override).');
  process.exit(0);
}

if (inputOverride && !fileExists(inputOverride)) {
  console.error(`[model-eval-gate] Dataset not found: ${inputOverride}`);
  process.exit(2);
}

const evaluations = selectedModels.length ? selectedModels : [null];
let failed = false;

for (const model of evaluations) {
  const dataset = resolveDataset(model);
  if (!dataset) {
    console.error('[model-eval-gate] Dataset not specified for model evaluation.');
    failed = true;
    break;
  }
  if (!fileExists(dataset)) {
    console.error(`[model-eval-gate] Dataset not found: ${dataset}`);
    failed = true;
    break;
  }

  const args = ['run', 'model:eval', '--', '--input', dataset];
  if (model?.name && aeirPath) {
    args.push('--aeir', aeirPath, '--model', model.name);
  }
  thresholdOverrides.forEach((override) => {
    args.push('--threshold', override);
  });

  if (model?.name) {
    const safeName = sanitizeName(model.name);
    const outputPath = path.join('artifacts', 'model-eval', `summary.${safeName}.json`);
    args.push('--output', outputPath);
  }

  console.log(`[model-eval-gate] Running: pnpm ${args.join(' ')}`);
  const result = spawnSync('pnpm', args, { stdio: 'inherit' });
  if (result.error) {
    console.error(`[model-eval-gate] Failed to run model-eval: ${String(result.error)}`);
    failed = true;
    break;
  }
  const exitCode = result.status ?? 1;
  if (exitCode !== 0) {
    failed = true;
    break;
  }
}

process.exit(failed ? 1 : 0);
