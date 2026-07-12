import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { describe, expect, it } from 'vitest';
import {
  buildCacheComparison,
  renderCacheComparisonMarkdown,
  run,
} from '../../scripts/actions/summarize-assurance-gate-cache-comparison.mjs';

const exactRef = 'b'.repeat(40);
const cacheKey = `ae-framework-core-pnpm-v1-Linux-X64-10.0.0-${'c'.repeat(64)}`;
const environment = {
  runnerOs: 'Linux',
  architecture: 'X64',
  runnerImage: 'ubuntu24-fixture',
  nodeVersion: 'v20.20.2',
  npmVersion: '10.8.2',
  pnpmVersion: '10.0.0',
};

function samples() {
  return ['cache-miss', 'cache-hit'].flatMap((mode) =>
    Array.from({ length: 5 }, (_, offset) => ({
      mode,
      index: offset + 1,
      exactRef,
      durationMs: (mode === 'cache-miss' ? 10_000 : 6_000) + offset,
      result: 'pass',
      stepOutcome: 'success',
      cacheEnabled: mode === 'cache-hit',
      cacheHit: mode === 'cache-hit',
      cacheKey,
      environment,
    })));
}

describe('assurance gate cache comparison', () => {
  it('builds a schema-valid 5+5 comparison and keeps the cache above target', () => {
    const report = buildCacheComparison({
      samples: samples(),
      exactRef,
      workflowRunId: 123,
      generatedAt: '2026-07-11T00:00:00Z',
    });
    const schema = JSON.parse(readFileSync(
      resolve('schema/assurance-gate-cache-comparison.schema.json'),
      'utf8',
    ));
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate(report), JSON.stringify(validate.errors)).toBe(true);
    expect(report.decision).toMatchObject({
      functionalParity: true,
      exactCacheHits: 5,
      targetMet: true,
      recommendedOutcome: 'keep-pnpm-store-cache',
    });
    expect(report.decision.improvementRatio).toBeCloseTo(0.4, 3);
  });

  it('preserves a rollback decision when an enabled sample misses the exact key', () => {
    const invalid = samples();
    invalid[5].cacheHit = false;
    const report = buildCacheComparison({
      samples: invalid,
      exactRef,
      workflowRunId: 123,
      generatedAt: '2026-07-11T00:00:00Z',
    });
    expect(report.decision).toMatchObject({
      exactCacheHits: 4,
      targetMet: false,
      recommendedOutcome: 'rollback-pnpm-store-cache',
    });
  });

  it('renders an overhead-only decision surface', () => {
    const report = buildCacheComparison({
      samples: samples(),
      exactRef,
      workflowRunId: 123,
      generatedAt: '2026-07-11T00:00:00Z',
    });
    const markdown = renderCacheComparisonMarkdown(report);
    expect(markdown).toContain('Median improvement: 39.99%');
    expect(markdown).toContain('not evidence of review speed, productivity, code quality');
  });

  it('aggregates downloaded sample artifacts and writes validated reports', () => {
    const tmpRoot = resolve('.codex-local/tmp/assurance-gate-cache-comparison-test');
    const inputDir = resolve(tmpRoot, 'samples');
    rmSync(tmpRoot, { recursive: true, force: true });
    for (const sample of samples()) {
      const directory = resolve(inputDir, `${sample.mode}-${sample.index}`);
      mkdirSync(directory, { recursive: true });
      writeFileSync(resolve(directory, 'sample.json'), `${JSON.stringify(sample, null, 2)}\n`);
    }
    const output = resolve(tmpRoot, 'comparison.json');
    const outputMd = resolve(tmpRoot, 'comparison.md');
    const result = run({
      inputDir,
      output,
      outputMd,
      schema: resolve('schema/assurance-gate-cache-comparison.schema.json'),
      exactRef,
      workflowRunId: 123,
      generatedAt: '2026-07-11T00:00:00Z',
    });
    expect(result.report.samples).toHaveLength(10);
    expect(JSON.parse(readFileSync(output, 'utf8')).decision.targetMet).toBe(true);
    expect(readFileSync(outputMd, 'utf8')).toContain('keep-pnpm-store-cache');
  });

  it('preserves the hosted rollback report as schema-valid reference evidence', () => {
    const report = JSON.parse(readFileSync(
      resolve('artifacts/reference/benchmarks/assurance-gate-cache-comparison-2026-07-11.json'),
      'utf8',
    ));
    const schema = JSON.parse(readFileSync(
      resolve('schema/assurance-gate-cache-comparison.schema.json'),
      'utf8',
    ));
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate(report), JSON.stringify(validate.errors)).toBe(true);
    expect(report).toMatchObject({
      exactRef: '7f2bed283cd5bd5550d91fec6e6d607d8d50f60a',
      workflowRunId: 29172844714,
      decision: {
        functionalParity: true,
        exactCacheHits: 5,
        targetMet: false,
        recommendedOutcome: 'rollback-pnpm-store-cache',
      },
    });
    expect(report.samples).toHaveLength(10);
    const pnpmVersions = report.samples.map(
      (sample: { environment: { pnpmVersion: string } }) => sample.environment.pnpmVersion,
    );
    expect(new Set(pnpmVersions)).toEqual(new Set(['10.0.0']));
  });

  it('keeps the measured cache experiment rolled back from both action entry points', () => {
    for (const actionPath of ['action.yml', '.github/actions/assurance-gate/action.yml']) {
      const action = readFileSync(resolve(actionPath), 'utf8');
      expect(action).not.toContain('dependency-cache:');
      expect(action).not.toContain('dependency-cache-hit:');
      expect(action).not.toContain('dependency-cache-key:');
      expect(action).not.toContain('uses: actions/cache/restore@v4');
      expect(action).not.toContain('uses: actions/cache/save@v4');
      expect(action).not.toContain('.cache/assurance-gate-pnpm-store');
    }
    expect(existsSync(resolve('.github/workflows/assurance-gate-cache-comparison.yml'))).toBe(false);
  });
});
