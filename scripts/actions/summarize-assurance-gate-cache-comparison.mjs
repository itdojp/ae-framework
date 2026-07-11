#!/usr/bin/env node

import { readdirSync, readFileSync, statSync, mkdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import {
  assertReportPath,
  summarizeValues,
} from './benchmark-assurance-gate-startup.mjs';

const DEFAULT_SCHEMA = 'schema/assurance-gate-cache-comparison.schema.json';

function parseArgs(argv) {
  const options = {
    inputDir: 'artifacts/benchmarks/cache-samples',
    output: 'artifacts/benchmarks/assurance-gate-cache-comparison.json',
    outputMd: 'artifacts/benchmarks/assurance-gate-cache-comparison.md',
    schema: DEFAULT_SCHEMA,
    exactRef: '',
    workflowRunId: 0,
    generatedAt: '',
    help: false,
  };
  for (const arg of argv.slice(2)) {
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') options.help = true;
    else if (arg.startsWith('--input-dir=')) options.inputDir = arg.slice('--input-dir='.length);
    else if (arg.startsWith('--output=')) options.output = arg.slice('--output='.length);
    else if (arg.startsWith('--output-md=')) options.outputMd = arg.slice('--output-md='.length);
    else if (arg.startsWith('--schema=')) options.schema = arg.slice('--schema='.length);
    else if (arg.startsWith('--exact-ref=')) options.exactRef = arg.slice('--exact-ref='.length);
    else if (arg.startsWith('--workflow-run-id=')) {
      options.workflowRunId = Number(arg.slice('--workflow-run-id='.length));
    } else if (arg.startsWith('--generated-at=')) {
      options.generatedAt = arg.slice('--generated-at='.length);
    } else throw new Error(`unknown argument: ${arg}`);
  }
  if (!options.help) {
    if (!/^[0-9a-f]{40}$/u.test(options.exactRef)) {
      throw new Error('--exact-ref must be a lowercase 40-character commit SHA');
    }
    if (!Number.isSafeInteger(options.workflowRunId) || options.workflowRunId < 1) {
      throw new Error('--workflow-run-id must be a positive integer');
    }
    if (options.generatedAt && Number.isNaN(Date.parse(options.generatedAt))) {
      throw new Error('--generated-at must be an ISO date-time');
    }
  }
  return options;
}

function printHelp() {
  process.stdout.write('Usage: node scripts/actions/summarize-assurance-gate-cache-comparison.mjs [options]\n');
  process.stdout.write('  --input-dir=<path>       downloaded cache sample artifacts\n');
  process.stdout.write('  --exact-ref=<sha>        exact measured commit SHA\n');
  process.stdout.write('  --workflow-run-id=<id>   GitHub Actions run ID\n');
  process.stdout.write('  --output=<path>          comparison JSON output\n');
  process.stdout.write('  --output-md=<path>       comparison Markdown output\n');
}

function assertInside(root, candidate, label) {
  const resolvedRoot = path.resolve(root);
  const resolved = path.resolve(candidate);
  const relative = path.relative(resolvedRoot, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`${label} must stay inside ${resolvedRoot}`);
  }
  return resolved;
}

function findSampleFiles(root) {
  const files = [];
  const visit = (directory) => {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      const candidate = path.join(directory, entry.name);
      if (entry.isDirectory()) visit(candidate);
      else if (entry.isFile() && entry.name === 'sample.json') files.push(candidate);
    }
  };
  visit(root);
  return files.sort();
}

function summarizeMode(samples) {
  return {
    sampleCount: samples.length,
    results: {
      pass: samples.filter((sample) => sample.result === 'pass').length,
      block: samples.filter((sample) => sample.result === 'block').length,
      error: samples.filter((sample) => sample.result === 'error').length,
    },
    durationMs: summarizeValues(samples.map((sample) => sample.durationMs)),
  };
}

function assertSamples(samples, exactRef) {
  if (samples.length !== 10) throw new Error(`expected 10 sample files, found ${samples.length}`);
  const runnerClasses = new Set(samples.map((sample) => JSON.stringify({
    runnerOs: sample.environment.runnerOs,
    architecture: sample.environment.architecture,
    runnerImage: sample.environment.runnerImage,
    nodeVersion: sample.environment.nodeVersion,
    npmVersion: sample.environment.npmVersion,
  })));
  if (runnerClasses.size !== 1) throw new Error('all samples must use the same runner/tool class');
  const cacheKeys = new Set(samples
    .map((sample) => sample.cacheKey)
    .filter((cacheKey) => cacheKey !== 'unavailable'));
  if (cacheKeys.size > 1) throw new Error('available samples must use the same exact cache key');

  for (const mode of ['cache-miss', 'cache-hit']) {
    const modeSamples = samples.filter((sample) => sample.mode === mode);
    if (modeSamples.length !== 5) throw new Error(`${mode} must contain exactly 5 samples`);
    const indices = modeSamples.map((sample) => sample.index).sort((left, right) => left - right);
    if (JSON.stringify(indices) !== JSON.stringify([1, 2, 3, 4, 5])) {
      throw new Error(`${mode} indices must be unique and contiguous from 1`);
    }
    for (const sample of modeSamples) {
      if (sample.exactRef !== exactRef) throw new Error(`${mode} sample ref does not match --exact-ref`);
      if (mode === 'cache-miss' && (sample.cacheEnabled || sample.cacheHit)) {
        throw new Error('cache-miss samples must disable the action cache and report cacheHit=false');
      }
      if (mode === 'cache-hit' && !sample.cacheEnabled) {
        throw new Error('cache-hit samples must enable the action cache');
      }
    }
  }
}

function validateReport(report, schemaPath) {
  const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  if (!validate(report)) {
    const detail = (validate.errors ?? [])
      .map((entry) => `${entry.instancePath || '/'}: ${entry.message || 'invalid'}`)
      .join('\n');
    throw new Error(`comparison schema validation failed:\n${detail}`);
  }
}

export function buildCacheComparison({ samples, exactRef, workflowRunId, generatedAt }) {
  assertSamples(samples, exactRef);
  const missSamples = samples.filter((sample) => sample.mode === 'cache-miss');
  const hitSamples = samples.filter((sample) => sample.mode === 'cache-hit');
  const summary = {
    cacheMiss: summarizeMode(missSamples),
    cacheHit: summarizeMode(hitSamples),
  };
  const pnpmVersions = new Set(samples.map((sample) => sample.environment.pnpmVersion));
  const functionalParity = pnpmVersions.size === 1
    && !pnpmVersions.has('unavailable')
    && samples.every((sample) => sample.result === 'pass' && sample.stepOutcome === 'success');
  const exactCacheHits = hitSamples.filter((sample) => sample.cacheHit).length;
  const improvementRatio = summary.cacheMiss.durationMs.median > 0
    ? (summary.cacheMiss.durationMs.median - summary.cacheHit.durationMs.median)
      / summary.cacheMiss.durationMs.median
    : 0;
  const targetMet = functionalParity && exactCacheHits === 5 && improvementRatio >= 0.2;
  return {
    schemaVersion: 'assurance-gate-cache-comparison/v1',
    generatedAt,
    exactRef,
    workflowRunId,
    fixture: {
      id: 'external-minimal-pass',
      expectedResult: 'pass',
      profile: 'minimal',
    },
    method: {
      sampleCountPerMode: 5,
      targetImprovementRatio: 0.2,
      totalBoundary: 'Elapsed time from immediately before the local composite action step until immediately after it, including package-manager setup, exact cache restore when enabled, install, build, gate execution, and review rendering.',
      cacheBoundary: 'Cache-disabled samples use a unique empty runner-temp pnpm store. Enabled samples restore only the action-owned pnpm content-addressable store with one exact OS/architecture/pnpm-version/lockfile-digest key; no restore prefixes, node_modules, build output, consumer artifacts, or gate results are cached.',
    },
    samples: [...samples].sort((left, right) =>
      left.mode.localeCompare(right.mode) || left.index - right.index),
    summary,
    decision: {
      functionalParity,
      exactCacheHits,
      improvementRatio,
      targetMet,
      recommendedOutcome: targetMet ? 'keep-pnpm-store-cache' : 'rollback-pnpm-store-cache',
    },
  };
}

export function renderCacheComparisonMarkdown(report) {
  const miss = report.summary.cacheMiss.durationMs;
  const hit = report.summary.cacheHit.durationMs;
  return [
    '# Assurance Gate pnpm-store cache comparison',
    '',
    `- Exact ref: \`${report.exactRef}\``,
    `- Workflow run: ${report.workflowRunId}`,
    `- Environment: ${report.samples[0].environment.runnerImage}, ${report.samples[0].environment.nodeVersion}, pnpm ${report.samples[0].environment.pnpmVersion}`,
    `- Samples: cache miss=${report.summary.cacheMiss.sampleCount}, exact cache hit=${report.summary.cacheHit.sampleCount}`,
    `- Functional parity: ${report.decision.functionalParity}`,
    `- Exact cache hits: ${report.decision.exactCacheHits}/5`,
    '',
    '| Mode | Minimum (ms) | Median (ms) | Maximum (ms) | p90 (ms) |',
    '| --- | ---: | ---: | ---: | ---: |',
    `| cache disabled/miss | ${miss.minimum.toFixed(2)} | ${miss.median.toFixed(2)} | ${miss.maximum.toFixed(2)} | ${miss.p90.toFixed(2)} |`,
    `| exact pnpm-store cache hit | ${hit.minimum.toFixed(2)} | ${hit.median.toFixed(2)} | ${hit.maximum.toFixed(2)} | ${hit.p90.toFixed(2)} |`,
    '',
    `- Median improvement: ${(report.decision.improvementRatio * 100).toFixed(2)}%`,
    `- 20% target met: ${report.decision.targetMet}`,
    `- Recommended outcome: \`${report.decision.recommendedOutcome}\``,
    '',
    '> This comparison measures action startup/runtime overhead only. It is not evidence of review speed, productivity, code quality, approval, or safety improvement.',
  ].join('\n');
}

export function run(options) {
  const repoRoot = process.cwd();
  const inputDir = assertInside(repoRoot, options.inputDir, 'input directory');
  if (!statSync(inputDir).isDirectory()) throw new Error('input directory must be a directory');
  const output = assertReportPath(repoRoot, options.output, '.json', 'JSON output');
  const outputMd = assertReportPath(repoRoot, options.outputMd, '.md', 'Markdown output');
  const schema = assertInside(repoRoot, options.schema, 'schema');
  const samples = findSampleFiles(inputDir).map((file) => JSON.parse(readFileSync(file, 'utf8')));
  const report = buildCacheComparison({
    samples,
    exactRef: options.exactRef,
    workflowRunId: options.workflowRunId,
    generatedAt: options.generatedAt || new Date().toISOString(),
  });
  validateReport(report, schema);
  mkdirSync(path.dirname(output), { recursive: true });
  mkdirSync(path.dirname(outputMd), { recursive: true });
  writeFileSync(output, `${JSON.stringify(report, null, 2)}\n`);
  writeFileSync(outputMd, `${renderCacheComparisonMarkdown(report)}\n`);
  return { report, output, outputMd };
}

function isExecutedAsMain(metaUrl, argvPath = process.argv[1]) {
  return Boolean(argvPath) && path.resolve(fileURLToPath(metaUrl)) === path.resolve(argvPath);
}

if (isExecutedAsMain(import.meta.url)) {
  try {
    const options = parseArgs(process.argv);
    if (options.help) printHelp();
    else {
      const result = run(options);
      process.stdout.write('Assurance Gate cache comparison: OK\n');
      process.stdout.write(`- JSON: ${path.relative(process.cwd(), result.output)}\n`);
      process.stdout.write(`- Markdown: ${path.relative(process.cwd(), result.outputMd)}\n`);
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`Assurance Gate cache comparison: FAILED\n${message}\n`);
    process.exitCode = 1;
  }
}
