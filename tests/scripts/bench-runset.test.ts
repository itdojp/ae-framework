import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

const repoRoot = resolve('.');
const runsetScript = resolve(repoRoot, 'scripts/ci/bench-runset.mjs');

function createBenchReport(schemaVersion = 'benchmark-report/v1') {
  return {
    schemaVersion,
    summary: [
      {
        name: 'noop',
        meanMs: 1.2,
        hz: 1000,
        sdMs: 0.12,
        samples: 30,
        p95: 100,
        errorRate: 0.1,
        coldStartMs: 50,
      },
    ],
    metrics: {
      p95: 100,
      errorRate: 0.1,
      coldStartMs: 50,
      peakRssMb: 100,
    },
    meta: {
      date: '2026-03-04T00:00:00.000Z',
    },
  };
}

describe.sequential('bench-runset script', () => {
  it('sorts and de-duplicates run files and writes runset output', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-runset-'));

    try {
      const run1 = join(tempDir, 'bench-ts-run1.json');
      const run2 = join(tempDir, 'bench-ts-run2.json');
      const out = join(tempDir, 'runset.txt');
      writeFileSync(run1, JSON.stringify(createBenchReport()), 'utf8');
      writeFileSync(run2, JSON.stringify(createBenchReport()), 'utf8');

      const result = spawnSync(
        'node',
        [runsetScript, '--absolute', '--out', out, run2, run1, run1],
        { encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout.trim()).toBe(`${run1},${run2}`);
      expect(readFileSync(out, 'utf8').trim()).toBe(`${run1},${run2}`);
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('fails when run count is lower than --min-runs', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-runset-min-'));

    try {
      const run1 = join(tempDir, 'bench-ts-run1.json');
      writeFileSync(run1, JSON.stringify(createBenchReport()), 'utf8');

      const result = spawnSync(
        'node',
        [runsetScript, '--min-runs', '2', run1],
        { encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('insufficient run files');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('fails when --min-runs is not an integer', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-runset-arg-'));

    try {
      const run1 = join(tempDir, 'bench-ts-run1.json');
      const run2 = join(tempDir, 'bench-ts-run2.json');
      writeFileSync(run1, JSON.stringify(createBenchReport()), 'utf8');
      writeFileSync(run2, JSON.stringify(createBenchReport()), 'utf8');

      const result = spawnSync(
        'node',
        [runsetScript, '--min-runs', '2x', run1, run2],
        { encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('--min-runs must be a positive integer');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('fails when schemaVersion does not match benchmark-report/v1', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-runset-schema-'));

    try {
      const run1 = join(tempDir, 'bench-ts-run1.json');
      const run2 = join(tempDir, 'bench-ts-run2.json');
      writeFileSync(run1, JSON.stringify(createBenchReport('benchmark-report/v2')), 'utf8');
      writeFileSync(run2, JSON.stringify(createBenchReport()), 'utf8');

      const result = spawnSync(
        'node',
        [runsetScript, run1, run2],
        { encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('schemaVersion mismatch');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });
});
