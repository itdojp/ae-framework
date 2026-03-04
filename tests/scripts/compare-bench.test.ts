import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

const repoRoot = resolve('.');
const compareScript = resolve(repoRoot, 'scripts/ci/compare-bench.mjs');

function createBenchSummary(meanMs: number, hz: number) {
  return {
    summary: [
      {
        name: 'noop',
        meanMs,
        hz,
      },
    ],
  };
}

describe.sequential('compare-bench script', () => {
  it('writes JSON artifact with --out-json when comparison passes', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-compare-bench-pass-'));

    try {
      const basePath = join(tempDir, 'base.json');
      const candidatePath = join(tempDir, 'candidate.json');
      const outPath = join(tempDir, 'bench-ts-compare.json');
      writeFileSync(basePath, JSON.stringify(createBenchSummary(10, 1000)), 'utf8');
      writeFileSync(candidatePath, JSON.stringify(createBenchSummary(10.2, 980)), 'utf8');

      const result = spawnSync(
        'node',
        [compareScript, basePath, candidatePath, '0.05', '--out-json', outPath],
        { encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const payload = JSON.parse(readFileSync(outPath, 'utf8')) as {
        ok: boolean;
        tol: number;
        rows: Array<{ pass: boolean }>;
      };
      expect(payload.ok).toBe(true);
      expect(payload.tol).toBe(0.05);
      expect(payload.rows).toHaveLength(1);
      expect(payload.rows[0]?.pass).toBe(true);
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('writes JSON artifact on threshold breach and exits with 1', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-compare-bench-fail-'));

    try {
      const basePath = join(tempDir, 'base.json');
      const candidatePath = join(tempDir, 'candidate.json');
      const outPath = join(tempDir, 'bench-ts-compare.json');
      writeFileSync(basePath, JSON.stringify(createBenchSummary(10, 1000)), 'utf8');
      writeFileSync(candidatePath, JSON.stringify(createBenchSummary(20, 500)), 'utf8');

      const result = spawnSync(
        'node',
        [compareScript, basePath, candidatePath, '--tolerance', '0.05', '--out-json', outPath],
        { encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status).toBe(1);
      expect(result.stdout).toContain('[bench-compare]');
      const payload = JSON.parse(readFileSync(outPath, 'utf8')) as {
        ok: boolean;
        rows: Array<{ pass: boolean }>;
      };
      expect(payload.ok).toBe(false);
      expect(payload.rows).toHaveLength(1);
      expect(payload.rows[0]?.pass).toBe(false);
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });
});
