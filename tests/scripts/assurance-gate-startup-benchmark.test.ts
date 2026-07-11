import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { describe, expect, it } from 'vitest';
import {
  assessOptimization,
  assertReportPath,
  assertScratchDirectory,
  normalizeExactRef,
  renderMarkdown,
  summarizeSamples,
  summarizeValues,
} from '../../scripts/actions/benchmark-assurance-gate-startup.mjs';
import { validateBenchmarkFiles } from '../../scripts/actions/validate-assurance-gate-startup-benchmark.mjs';

const repoRoot = resolve('.');
const schema = JSON.parse(readFileSync(
  resolve('schema/assurance-gate-startup-benchmark.schema.json'),
  'utf8',
)) as Record<string, unknown>;

function sample(cacheState: 'cold' | 'warm', index: number, total: number) {
  return {
    cacheState,
    index,
    result: 'pass',
    phaseTimingsMs: {
      actionInitialization: 10 + index,
      corepackPnpmSetup: cacheState === 'cold' ? 5_000 + index : 500 + index,
      dependencyInstall: cacheState === 'cold' ? 65_000 + index : 1_000 + index,
      coreBuild: cacheState === 'cold' ? 12_000 + index : 2_000 + index,
      gateExecution: 3_000 + index,
      reviewSurfaceRendering: 10 + index,
      total: total + index,
    },
  };
}

function fixtureReport() {
  const coldSamples = Array.from({ length: 5 }, (_, index) => sample('cold', index + 1, 100_000));
  const warmSamples = Array.from({ length: 5 }, (_, index) => sample('warm', index + 1, 7_000));
  const summary = {
    cold: summarizeSamples(coldSamples),
    warm: summarizeSamples(warmSamples),
  };
  return {
    schemaVersion: 'assurance-gate-startup-benchmark/v1',
    generatedAt: '2026-07-11T00:00:00Z',
    exactRef: 'a'.repeat(40),
    fixture: {
      id: 'external-minimal-pass',
      expectedResult: 'pass',
      profile: 'minimal',
    },
    environment: {
      runnerOs: 'linux',
      architecture: 'x64',
      runnerImage: 'ubuntu-24.04',
      cpu: 'fixture-cpu',
      totalMemoryBytes: 1024,
      nodeVersion: 'v20.19.0',
      npmVersion: '10.8.2',
      pnpmVersion: '10.0.0',
      pnpmVersionSource: 'measured',
    },
    method: {
      runCountPerCacheState: 5,
      checkoutInitializationMs: 123,
      pilotFriction: 'not-observed',
      coldDefinition: 'fresh store and install state',
      warmDefinition: 'preconditioned store and install state',
      reviewSurfaceTimingBoundary: 'review rendering is nested in gate execution',
    },
    collectionErrors: [],
    samples: [...coldSamples, ...warmSamples],
    summary,
    optimizationAssessment: assessOptimization(summary, 'not-observed'),
  };
}

describe('assurance gate startup benchmark contract', () => {
  it('normalizes exact commit SHAs and rejects ambiguous refs', () => {
    expect(normalizeExactRef('A'.repeat(40))).toBe('a'.repeat(40));
    expect(() => normalizeExactRef('main')).toThrow('exact 40-character hexadecimal commit SHA');
  });

  it('limits destructive benchmark work to a named child of .codex-local/tmp', () => {
    expect(() => assertScratchDirectory(repoRoot, repoRoot)).toThrow('must stay inside');
    expect(() => assertScratchDirectory(
      repoRoot,
      resolve('.codex-local/tmp'),
    )).toThrow('must be a child');
    expect(assertScratchDirectory(
      repoRoot,
      resolve('.codex-local/tmp/startup-safe'),
    )).toBe(resolve('.codex-local/tmp/startup-safe'));
  });

  it('limits report writes to benchmark artifact or local scratch paths', () => {
    expect(() => assertReportPath(repoRoot, resolve('package.json'), '.json', 'JSON output'))
      .toThrow('must be a file under');
    expect(() => assertReportPath(
      repoRoot,
      resolve('artifacts/benchmarks/report.md'),
      '.json',
      'JSON output',
    )).toThrow('must use the .json extension');
    expect(assertReportPath(
      repoRoot,
      resolve('.codex-local/tmp/report.json'),
      '.json',
      'JSON output',
    )).toBe(resolve('.codex-local/tmp/report.json'));
  });

  it('computes deterministic median/min/max/p90 statistics', () => {
    expect(summarizeValues([5, 1, 4, 2, 3])).toEqual({
      minimum: 1,
      median: 3,
      maximum: 5,
      p90: 5,
    });
  });

  it('validates a cold/warm five-sample report and its standalone validator', () => {
    const report = fixtureReport();
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate(report), JSON.stringify(validate.errors)).toBe(true);
    expect(report.optimizationAssessment.triggers.coldMedianOver60Seconds).toBe(true);
    expect(report.optimizationAssessment.triggers.setupInstallBuildOver70Percent).toBe(true);

    const tmpRoot = resolve('.codex-local/tmp/assurance-gate-startup-contract-test');
    rmSync(tmpRoot, { recursive: true, force: true });
    mkdirSync(tmpRoot, { recursive: true });
    const reportPath = resolve(tmpRoot, 'report.json');
    writeFileSync(reportPath, `${JSON.stringify(report, null, 2)}\n`);
    expect(validateBenchmarkFiles({
      reportPath,
      schemaPath: resolve('schema/assurance-gate-startup-benchmark.schema.json'),
    }).valid).toBe(true);
  });

  it('rejects a report whose cache-state count disagrees with the method', () => {
    const report = fixtureReport();
    report.samples.push(sample('warm', 6, 7_000));
    const tmpRoot = resolve('.codex-local/tmp/assurance-gate-startup-count-test');
    rmSync(tmpRoot, { recursive: true, force: true });
    mkdirSync(tmpRoot, { recursive: true });
    const reportPath = resolve(tmpRoot, 'report.json');
    writeFileSync(reportPath, `${JSON.stringify(report, null, 2)}\n`);

    const result = validateBenchmarkFiles({
      reportPath,
      schemaPath: resolve('schema/assurance-gate-startup-benchmark.schema.json'),
    });
    expect(result.valid).toBe(false);
    expect(result.errors).toContainEqual(expect.objectContaining({
      message: 'must not contain more than 5 warm samples',
    }));
  });

  it('preserves a valid diagnostic report when warm preconditioning prevents samples', () => {
    const report = fixtureReport();
    report.samples = report.samples.filter((entry) => entry.cacheState === 'cold');
    report.summary.warm = summarizeSamples([]);
    report.collectionErrors = [{
      cacheState: 'warm',
      stage: 'warmPreconditioning',
      phase: 'dependencyInstall',
      missingSampleCount: 5,
    }];
    const tmpRoot = resolve('.codex-local/tmp/assurance-gate-startup-collection-error-test');
    rmSync(tmpRoot, { recursive: true, force: true });
    mkdirSync(tmpRoot, { recursive: true });
    const reportPath = resolve(tmpRoot, 'report.json');
    writeFileSync(reportPath, `${JSON.stringify(report, null, 2)}\n`);

    const result = validateBenchmarkFiles({
      reportPath,
      schemaPath: resolve('schema/assurance-gate-startup-benchmark.schema.json'),
    });
    expect(result.valid, JSON.stringify(result.errors)).toBe(true);
    expect(renderMarkdown(report)).toContain('warm/warmPreconditioning/dependencyInstall');
  });

  it('rejects missing cold samples without crashing semantic validation', () => {
    const report = fixtureReport();
    report.samples = report.samples.filter((entry) => entry.cacheState === 'warm');
    report.summary.cold = summarizeSamples([]);
    const tmpRoot = resolve('.codex-local/tmp/assurance-gate-startup-missing-cold-test');
    rmSync(tmpRoot, { recursive: true, force: true });
    mkdirSync(tmpRoot, { recursive: true });
    const reportPath = resolve(tmpRoot, 'report.json');
    writeFileSync(reportPath, `${JSON.stringify(report, null, 2)}\n`);

    const result = validateBenchmarkFiles({
      reportPath,
      schemaPath: resolve('schema/assurance-gate-startup-benchmark.schema.json'),
    });
    expect(result.valid).toBe(false);
    expect(result.errors).toContainEqual(expect.objectContaining({
      message: 'cold samples are required to evaluate the optimization decision',
    }));
  });

  it('rejects summaries that were not derived from measured samples', () => {
    const report = fixtureReport();
    report.summary.cold.phaseTimingsMs.total.median += 1;
    const tmpRoot = resolve('.codex-local/tmp/assurance-gate-startup-summary-test');
    rmSync(tmpRoot, { recursive: true, force: true });
    mkdirSync(tmpRoot, { recursive: true });
    const reportPath = resolve(tmpRoot, 'report.json');
    writeFileSync(reportPath, `${JSON.stringify(report, null, 2)}\n`);

    const result = validateBenchmarkFiles({
      reportPath,
      schemaPath: resolve('schema/assurance-gate-startup-benchmark.schema.json'),
    });
    expect(result.valid).toBe(false);
    expect(result.errors).toContainEqual(expect.objectContaining({
      instancePath: '/summary/cold/phaseTimingsMs/total/median',
    }));
  });

  it('derives pilot friction from method input rather than the reported trigger', () => {
    const report = fixtureReport();
    report.optimizationAssessment.triggers.livePilotFrictionObserved = true;
    const tmpRoot = resolve('.codex-local/tmp/assurance-gate-startup-friction-test');
    rmSync(tmpRoot, { recursive: true, force: true });
    mkdirSync(tmpRoot, { recursive: true });
    const reportPath = resolve(tmpRoot, 'report.json');
    writeFileSync(reportPath, `${JSON.stringify(report, null, 2)}\n`);

    const result = validateBenchmarkFiles({
      reportPath,
      schemaPath: resolve('schema/assurance-gate-startup-benchmark.schema.json'),
    });
    expect(result.valid).toBe(false);
    expect(result.errors).toContainEqual(expect.objectContaining({
      instancePath: '/optimizationAssessment/triggers/livePilotFrictionObserved',
    }));
  });

  it('accepts an explicit error sample without hiding it in result counts', () => {
    const report = fixtureReport();
    report.samples[0].result = 'error';
    Object.assign(report.samples[0], { errorPhase: 'coreBuild' });
    report.summary.cold = summarizeSamples(report.samples.filter(
      (entry) => entry.cacheState === 'cold',
    ));
    report.optimizationAssessment = assessOptimization(report.summary, 'not-observed');
    const tmpRoot = resolve('.codex-local/tmp/assurance-gate-startup-error-test');
    rmSync(tmpRoot, { recursive: true, force: true });
    mkdirSync(tmpRoot, { recursive: true });
    const reportPath = resolve(tmpRoot, 'report.json');
    writeFileSync(reportPath, `${JSON.stringify(report, null, 2)}\n`);

    const result = validateBenchmarkFiles({
      reportPath,
      schemaPath: resolve('schema/assurance-gate-startup-benchmark.schema.json'),
    });
    expect(result.valid, JSON.stringify(result.errors)).toBe(true);
    expect(result.report.summary.cold.results.error).toBe(1);
    expect(renderMarkdown(report)).toContain('- cold #1: coreBuild');
  });

  it('renders an overhead-only report and leaves final decision pending review', () => {
    const report = fixtureReport();
    const markdown = renderMarkdown(report);

    expect(markdown).toContain('Final decision: `pending-reviewed-baseline`');
    expect(markdown).toContain('Workflow checkout/initialization: 123.00 ms');
    expect(markdown).toContain('Cold results: pass=5, block=0, error=0');
    expect(markdown).toContain('not evidence of review speed, productivity, code quality');
  });

  it('keeps the benchmark workflow manual/scheduled and outside pull_request gates', () => {
    const workflow = readFileSync(
      resolve('.github/workflows/assurance-gate-startup-benchmark.yml'),
      'utf8',
    );

    expect(workflow).toContain('workflow_dispatch:');
    expect(workflow).toContain('schedule:');
    expect(workflow).not.toContain('pull_request:');
    expect(workflow).toContain('assurance-gate-startup-report-only');
    expect(workflow).toContain('timeout-minutes: 90');
    expect(workflow).toContain('uses: actions/setup-node@v4');
    expect(workflow).not.toContain('uses: ./.github/actions/setup-node-pnpm');
  });

  it('provides a no-side-effect help path', () => {
    const result = spawnSync('node', [
      'scripts/actions/benchmark-assurance-gate-startup.mjs',
      '--',
      '--help',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 10_000,
    });

    expect(result.status, result.stderr).toBe(0);
    expect(result.stdout).toContain('--runs=5');
  });
});
