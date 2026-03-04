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
  taskName?: string;
}) {
  return {
    schemaVersion: 'benchmark-report/v1',
    summary: [
      {
        name: metrics.taskName ?? 'noop',
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
      expect(markdown).toContain('| go | 1 | PASS |');
      expect(markdown).toContain('| rust | 1 | FAIL |');
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

  it('treats zero baseline metrics as non-applicable ratio checks', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-compare-zero-baseline-'));

    try {
      const baselinePath = join(tempDir, 'baseline.json');
      const goPath = join(tempDir, 'go.json');
      const outJsonPath = join(tempDir, 'bench-compare.json');
      const outMdPath = join(tempDir, 'bench-compare.md');

      writeFileSync(
        baselinePath,
        JSON.stringify(createBenchReport({
          p95: 0,
          errorRate: 0.1,
          coldStartMs: 0,
          peakRssMb: 0,
          hz: 1000,
        })),
        'utf8',
      );
      writeFileSync(
        goPath,
        JSON.stringify(createBenchReport({
          p95: 5,
          errorRate: 0.2,
          coldStartMs: 10,
          peakRssMb: 50,
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
          `go=${goPath}`,
          '--out-json',
          outJsonPath,
          '--out-md',
          outMdPath,
          '--fail-on-threshold-breach',
        ],
        { encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status).toBe(0);
      const payload = JSON.parse(readFileSync(outJsonPath, 'utf8')) as {
        candidates: Array<{ overall: string; comparison: { p95Ratio: number | null } }>;
      };
      expect(payload.candidates[0]?.comparison.p95Ratio).toBeNull();
      expect(payload.candidates[0]?.overall).toBe('pass');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('fails on invalid benchmark-report inputs', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-compare-invalid-'));

    try {
      const baselinePath = join(tempDir, 'baseline.json');
      const candidatePath = join(tempDir, 'candidate.json');
      const outJsonPath = join(tempDir, 'bench-compare.json');
      const outMdPath = join(tempDir, 'bench-compare.md');

      const baseline = createBenchReport({
        p95: 100,
        errorRate: 0.1,
        coldStartMs: 50,
        peakRssMb: 100,
        hz: 1000,
      });
      baseline.summary = [];
      writeFileSync(baselinePath, JSON.stringify(baseline), 'utf8');

      const candidate = createBenchReport({
        p95: 80,
        errorRate: 110,
        coldStartMs: 45,
        peakRssMb: 95,
        hz: 1300,
      });
      writeFileSync(candidatePath, JSON.stringify(candidate), 'utf8');

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

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('summary must be a non-empty array');

      const validBaseline = createBenchReport({
        p95: 100,
        errorRate: 0.1,
        coldStartMs: 50,
        peakRssMb: 100,
        hz: 1000,
      });
      writeFileSync(baselinePath, JSON.stringify(validBaseline), 'utf8');

      const resultWithInvalidErrorRate = spawnSync(
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
      expect(resultWithInvalidErrorRate.status).toBe(1);
      expect(resultWithInvalidErrorRate.stderr).toContain('metrics.errorRate must be <= 100');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('supports multi-run input and computes CV checks', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-compare-multi-run-'));

    try {
      const baseline1Path = join(tempDir, 'baseline-1.json');
      const baseline2Path = join(tempDir, 'baseline-2.json');
      const go1Path = join(tempDir, 'go-1.json');
      const go2Path = join(tempDir, 'go-2.json');
      const outJsonPath = join(tempDir, 'bench-compare.json');
      const outMdPath = join(tempDir, 'bench-compare.md');

      writeFileSync(
        baseline1Path,
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
        baseline2Path,
        JSON.stringify(createBenchReport({
          p95: 100.2,
          errorRate: 0.1,
          coldStartMs: 50.1,
          peakRssMb: 100.1,
          hz: 1002,
        })),
        'utf8',
      );
      writeFileSync(
        go1Path,
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
        go2Path,
        JSON.stringify(createBenchReport({
          p95: 82,
          errorRate: 0.2,
          coldStartMs: 45,
          peakRssMb: 105,
          hz: 900,
        })),
        'utf8',
      );

      const result = spawnSync(
        'node',
        [
          compareScript,
          '--baseline',
          `${baseline1Path},${baseline2Path}`,
          '--candidate',
          `go=${go1Path},${go2Path}`,
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
        baseline: { runCount: number; reproducibility: { p95Cv: number | null } };
        candidates: Array<{
          name: string;
          runCount: number;
          reproducibility: { throughputCv: number | null };
          checks: { throughputCv: boolean };
          overall: string;
        }>;
      };

      expect(payload.baseline.runCount).toBe(2);
      expect(payload.baseline.reproducibility.p95Cv).not.toBeNull();
      expect(payload.candidates[0]?.name).toBe('go');
      expect(payload.candidates[0]?.runCount).toBe(2);
      expect(payload.candidates[0]?.reproducibility.throughputCv).not.toBeNull();
      expect(payload.candidates[0]?.checks.throughputCv).toBe(false);
      expect(payload.candidates[0]?.overall).toBe('fail');

      const markdown = readFileSync(outMdPath, 'utf8');
      expect(markdown).toMatch(/\|\s*go\s*\|\s*2\s*\|\s*FAIL\s*\|/);
      expect(markdown).toContain('throughput CV');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('fails when multi-run inputs have inconsistent summary shape', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-compare-shape-mismatch-'));

    try {
      const baseline1Path = join(tempDir, 'baseline-1.json');
      const baseline2Path = join(tempDir, 'baseline-2.json');
      const candidatePath = join(tempDir, 'candidate.json');
      const outJsonPath = join(tempDir, 'bench-compare.json');
      const outMdPath = join(tempDir, 'bench-compare.md');

      const baseline1 = createBenchReport({
        p95: 100,
        errorRate: 0.1,
        coldStartMs: 50,
        peakRssMb: 100,
        hz: 1000,
        taskName: 'task-A',
      });
      const baseline2 = createBenchReport({
        p95: 101,
        errorRate: 0.1,
        coldStartMs: 50,
        peakRssMb: 100,
        hz: 1000,
        taskName: 'task-A',
      });
      baseline2.summary.push({
        name: 'task-B',
        meanMs: 1.0,
        hz: 500,
        sdMs: 0.1,
        samples: 30,
        p95: 90,
        errorRate: 0.1,
        coldStartMs: 45,
      });
      const candidate = createBenchReport({
        p95: 80,
        errorRate: 0.2,
        coldStartMs: 45,
        peakRssMb: 105,
        hz: 1300,
        taskName: 'task-A',
      });

      writeFileSync(baseline1Path, JSON.stringify(baseline1), 'utf8');
      writeFileSync(baseline2Path, JSON.stringify(baseline2), 'utf8');
      writeFileSync(candidatePath, JSON.stringify(candidate), 'utf8');

      const resultWithTaskCountMismatch = spawnSync(
        'node',
        [
          compareScript,
          '--baseline',
          `${baseline1Path},${baseline2Path}`,
          '--candidate',
          `go=${candidatePath}`,
          '--out-json',
          outJsonPath,
          '--out-md',
          outMdPath,
        ],
        { encoding: 'utf8', timeout: 120_000 },
      );
      expect(resultWithTaskCountMismatch.status).toBe(1);
      expect(resultWithTaskCountMismatch.stderr).toContain('inconsistent summary task count across runs');

      const baseline3 = createBenchReport({
        p95: 101,
        errorRate: 0.1,
        coldStartMs: 50,
        peakRssMb: 100,
        hz: 1000,
        taskName: 'task-Z',
      });
      writeFileSync(baseline2Path, JSON.stringify(baseline3), 'utf8');

      const resultWithTaskIdentityMismatch = spawnSync(
        'node',
        [
          compareScript,
          '--baseline',
          `${baseline1Path},${baseline2Path}`,
          '--candidate',
          `go=${candidatePath}`,
          '--out-json',
          outJsonPath,
          '--out-md',
          outMdPath,
        ],
        { encoding: 'utf8', timeout: 120_000 },
      );
      expect(resultWithTaskIdentityMismatch.status).toBe(1);
      expect(resultWithTaskIdentityMismatch.stderr).toContain('inconsistent summary task identities across runs');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });
});
