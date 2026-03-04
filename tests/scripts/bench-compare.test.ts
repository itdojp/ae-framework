import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

const repoRoot = resolve('.');
const compareScript = resolve(repoRoot, 'scripts/quality/bench-compare.mjs');

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

describe.sequential('bench-compare script', () => {
  it('writes comparison JSON/Markdown and evaluates thresholds', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-compare-'));

    try {
      const baselinePath = join(tempDir, 'baseline.json');
      const goPath = join(tempDir, 'go.json');
      const rustPath = join(tempDir, 'rust.json');
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
        goPath,
        JSON.stringify(createBenchReport({
          p95: 80,
          errorRate: 0.2,
          coldStartMs: 45,
          peakRssMb: 105,
          hz: 1300,
        })),
        'utf8',
      );
      writeFileSync(
        rustPath,
        JSON.stringify(createBenchReport({
          p95: 95,
          errorRate: 0.8,
          coldStartMs: 70,
          peakRssMb: 130,
          hz: 1100,
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
          `go=${goPath}`,
          '--candidate',
          `rust=${rustPath}`,
          '--out-json',
          outJsonPath,
          '--out-md',
          outMdPath,
          '--fail-on-threshold-breach',
        ],
        { encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status).toBe(1);

      const payload = JSON.parse(readFileSync(outJsonPath, 'utf8')) as {
        schemaVersion: string;
        candidates: Array<{ name: string; overall: string; checks: { throughput: boolean } }>;
      };
      const markdown = readFileSync(outMdPath, 'utf8');

      expect(payload.schemaVersion).toBe('bench-compare/v1');
      expect(payload.candidates).toHaveLength(2);
      expect(payload.candidates.find((candidate) => candidate.name === 'go')?.overall).toBe('pass');
      expect(payload.candidates.find((candidate) => candidate.name === 'rust')?.overall).toBe('fail');
      expect(payload.candidates.find((candidate) => candidate.name === 'go')?.checks.throughput).toBe(true);
      expect(markdown).toContain('# Bench Comparison Report');
      expect(markdown).toContain('| go | PASS |');
      expect(markdown).toContain('| rust | FAIL |');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('fails when required arguments are missing', () => {
    const result = spawnSync('node', [compareScript], {
      encoding: 'utf8',
      timeout: 120_000,
    });

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('--baseline is required');
  });
});
