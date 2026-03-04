import { describe, expect, it } from 'vitest';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

const repoRoot = resolve('.');
const schemaPath = resolve(repoRoot, 'schema/bench-compare.schema.json');
const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));
const compareScript = resolve(repoRoot, 'scripts/quality/bench-compare.mjs');

function createValidator() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
}

function createBenchReport(metrics: {
  p95: number;
  errorRate: number;
  coldStartMs: number;
  peakRssMb: number;
  hz: number;
}) {
  return {
    schemaVersion: 'benchmark-report/v1',
    summary: [
      {
        name: 'noop',
        meanMs: 1.2,
        hz: metrics.hz,
        sdMs: 0.12,
        samples: 30,
        p95: metrics.p95,
        errorRate: metrics.errorRate,
        coldStartMs: metrics.coldStartMs,
      },
    ],
    metrics: {
      p95: metrics.p95,
      errorRate: metrics.errorRate,
      coldStartMs: metrics.coldStartMs,
      peakRssMb: metrics.peakRssMb,
    },
    meta: {
      date: '2026-03-04T00:00:00.000Z',
      env: {
        node: process.version,
        platform: process.platform,
        arch: process.arch,
        cpu: 'unit-test-cpu',
        totalMem: 1024,
        seed: 12345,
      },
      config: {
        warmupMs: 300,
        iterations: 30,
        seed: 12345,
      },
    },
  };
}

describe.sequential('bench-compare schema', () => {
  it('generated bench-compare.json conforms to schema', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-compare-schema-'));

    try {
      const baselinePath = join(tempDir, 'baseline.json');
      const candidatePath = join(tempDir, 'go.json');
      const outJsonPath = join(tempDir, 'bench-compare.json');
      const outMdPath = join(tempDir, 'bench-compare.md');

      writeFileSync(
        baselinePath,
        JSON.stringify(createBenchReport({
          p95: 100,
          errorRate: 0.1,
          coldStartMs: 50,
          peakRssMb: 100,
          hz: 1000,
        })),
        'utf8',
      );
      writeFileSync(
        candidatePath,
        JSON.stringify(createBenchReport({
          p95: 80,
          errorRate: 0.2,
          coldStartMs: 45,
          peakRssMb: 105,
          hz: 1300,
        })),
        'utf8',
      );

      const result = spawnSync(
        'node',
        [
          compareScript,
          '--baseline',
          baselinePath,
          '--candidate',
          `go=${candidatePath}`,
          '--out-json',
          outJsonPath,
          '--out-md',
          outMdPath,
        ],
        { encoding: 'utf8', timeout: 120_000 },
      );
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const payload = JSON.parse(readFileSync(outJsonPath, 'utf8')) as Record<string, unknown>;
      const validate = createValidator();
      expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);
      expect(payload['schemaVersion']).toBe('bench-compare/v1');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('rejects payload missing required checks', () => {
    const validate = createValidator();
    const payload = {
      schemaVersion: 'bench-compare/v1',
      generatedAt: '2026-03-04T00:00:00.000Z',
      baseline: {
        path: 'artifacts/bench.json',
        metrics: {
          p95: 10,
          errorRate: 0.1,
          coldStartMs: 20,
          peakRssMb: 120,
        },
        throughputHz: 2000,
        taskCount: 1,
      },
      candidates: [
        {
          name: 'go',
          path: 'artifacts/bench-go.json',
          metrics: {
            p95: 8,
            errorRate: 0.2,
            coldStartMs: 18,
            peakRssMb: 110,
          },
          throughputHz: 2500,
          comparison: {
            p95Ratio: 0.8,
            throughputRatio: 1.25,
            coldStartRatio: 0.9,
            peakRssRatio: 0.92,
            errorRateLimit: 0.5,
            errorRateDeltaPt: 0.1,
          },
          overall: 'pass',
        },
      ],
    };

    expect(validate(payload)).toBe(false);
  });
});
