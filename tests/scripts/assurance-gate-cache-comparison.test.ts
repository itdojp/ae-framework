import { mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
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

  it('keeps both composite actions on exact-key store-only caching', () => {
    for (const actionPath of ['action.yml', '.github/actions/assurance-gate/action.yml']) {
      const action = readFileSync(resolve(actionPath), 'utf8');
      expect(action).toContain('uses: actions/cache/restore@v4');
      expect(action).toContain('uses: actions/cache/save@v4');
      expect(action).toContain('key: ${{ steps.package-manager.outputs.cache-key }}');
      expect(action).not.toContain('restore-keys:');
      expect(action).not.toMatch(/path:.*node_modules/u);
      expect(action).toContain('.cache/assurance-gate-pnpm-store');
      expect(action).not.toContain('pnpm store path');
      expect(action).toContain('rm -rf -- "$AE_ACTION_STORE_PATH"');
      expect(action).toContain('dependency-cache-hit:');
      expect(action).toContain('dependency-cache-key:');
      expect(action).toContain('pnpm-version:');
      expect(action).toContain('pnpm-version=${pnpm_version}');
      expect(action).toContain("steps.dependency-cache.outputs.cache-hit == 'true'");
      expect(action).toMatch(/dependency-cache:\n(?:.*\n){1,3}\s+default: "false"/u);
    }
  });

  it('keeps the comparison workflow manual and outside normal PR gates', () => {
    const workflow = readFileSync(
      resolve('.github/workflows/assurance-gate-cache-comparison.yml'),
      'utf8',
    );
    expect(workflow).toContain('workflow_dispatch:');
    expect(workflow).not.toContain('pull_request:');
    expect(workflow).toContain('cache-miss-sample');
    expect(workflow).toContain('cache-hit-sample');
    expect(workflow).toContain('SAMPLE_COUNT_PER_MODE: 5');
    expect(workflow).toContain('NPM_CONFIG_STORE_DIR: ${{ runner.temp }}/assurance-gate-cache-miss-${{ matrix.index }}');
    expect(workflow.match(/PNPM_VERSION: \$\{\{ steps\.assurance\.outputs\.pnpm-version \}\}/gu)).toHaveLength(2);
    expect(workflow).not.toContain("pnpmVersion: version('pnpm')");
  });
});
