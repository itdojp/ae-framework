import { describe, expect, it } from 'vitest';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { existsSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

const repoRoot = resolve('.');
const schemaPath = resolve(repoRoot, 'schema/benchmark-report.schema.json');
const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));
const tsxBin = resolve(repoRoot, 'node_modules/.bin/tsx');
// benchmark-report/v1 is currently emitted through the legacy compatibility
// shim until benchmark artifact generation is migrated to a canonical CLI path.
const legacyBenchShimEntry = resolve(repoRoot, 'src/cli.ts');

function createValidator() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
}

describe.sequential('benchmark report schema', () => {
  it('bench run emits schema-conformant JSON artifact with required metrics', async () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-bench-schema-'));

    try {
      const env: NodeJS.ProcessEnv = {
        ...process.env,
        NODE_ENV: 'production',
        AE_TEST_NO_EXIT: '0',
        AE_SEED: '12345',
      };
      delete env.VITEST;

      const runResult = spawnSync(tsxBin, [legacyBenchShimEntry, 'bench'], {
        cwd: tempDir,
        encoding: 'utf8',
        timeout: 120_000,
        env,
      });
      expect(runResult.status, runResult.stderr || runResult.stdout).toBe(0);

      const outputPath = join(tempDir, 'artifacts', 'reference', 'benchmarks', 'bench.json');
      expect(existsSync(outputPath)).toBe(true);

      const payload = JSON.parse(readFileSync(outputPath, 'utf8')) as Record<string, unknown>;
      const validate = createValidator();

      expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);
      expect(payload['schemaVersion']).toBe('benchmark-report/v1');
      expect(payload['metrics']).toEqual(
        expect.objectContaining({
          p95: expect.any(Number),
          errorRate: expect.any(Number),
          coldStartMs: expect.any(Number),
          peakRssMb: expect.any(Number),
        }),
      );
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('rejects payload missing required benchmark metrics', () => {
    const validate = createValidator();
    const payload = {
      schemaVersion: 'benchmark-report/v1',
      summary: [
        {
          name: 'noop',
          meanMs: 0.012,
          hz: 1000,
          sdMs: 0.001,
          samples: 30,
          p95: 0.02,
          errorRate: 0,
          coldStartMs: 0.03,
        },
      ],
      metrics: {
        p95: 0.02,
        errorRate: 0,
        coldStartMs: 0.03,
      },
      meta: {
        date: '2026-03-04T00:00:00Z',
        env: {
          node: 'v22.0.0',
          platform: 'linux',
          arch: 'x64',
          cpu: 'test-cpu',
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

    expect(validate(payload)).toBe(false);
  });
});
