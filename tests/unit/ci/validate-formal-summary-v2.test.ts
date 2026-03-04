import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const validateScript = join(process.cwd(), 'scripts/ci/validate-formal-summary-v2.mjs');
const schemaPath = join(process.cwd(), 'schema/formal-summary-v2.schema.json');

describe('validate-formal-summary-v2 CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'formal-summary-v2-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('accepts valid formal summary v2', async () => {
    const summaryPath = join(workdir, 'formal-summary-v2.json');
    const summary = {
      schemaVersion: 'formal-summary/v2',
      contractId: 'formal-summary.v2',
      tool: 'aggregate',
      status: 'ok',
      ok: true,
      generatedAtUtc: '2026-03-04T00:00:00.000Z',
      metadata: {
        generatedAtUtc: '2026-03-04T00:00:00.000Z',
        generatedAtLocal: '2026-03-04T09:00:00.000+09:00',
        timezoneOffset: '+09:00',
        gitCommit: '0123456789abcdef0123456789abcdef01234567',
        branch: 'main',
        runner: {
          name: 'local',
          os: 'linux',
          arch: 'x64',
          ci: false,
        },
        toolVersions: {
          node: 'v22.0.0',
        },
      },
      results: [
        {
          name: 'conformance',
          status: 'ok',
          code: 0,
          durationMs: 12,
          logPath: 'artifacts/hermetic-reports/conformance/summary.json',
          reason: null,
        },
      ],
    };
    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(0);
    expect(result.stderr.toString()).toBe('');
  });

  it('fails for invalid contractId', async () => {
    const summaryPath = join(workdir, 'formal-summary-v2.json');
    const summary = {
      schemaVersion: 'formal-summary/v2',
      contractId: 'formal-summary.v1',
      tool: 'aggregate',
      status: 'ok',
      ok: true,
      generatedAtUtc: '2026-03-04T00:00:00.000Z',
      metadata: {
        generatedAtUtc: '2026-03-04T00:00:00.000Z',
        generatedAtLocal: '2026-03-04T09:00:00.000+09:00',
        timezoneOffset: '+09:00',
        gitCommit: '0123456789abcdef0123456789abcdef01234567',
        branch: 'main',
        runner: {
          name: 'local',
          os: 'linux',
          arch: 'x64',
          ci: false,
        },
        toolVersions: {
          node: 'v22.0.0',
        },
      },
      results: [],
    };
    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('schema validation failed');
  });
});
