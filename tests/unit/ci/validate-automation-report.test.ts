import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const validateScript = join(process.cwd(), 'scripts/ci/validate-automation-report.mjs');
const schemaPath = join(process.cwd(), 'schema/automation-observability-v1.schema.json');

describe('validate-automation-report CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'automation-report-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('accepts valid automation report', async () => {
    const reportPath = join(workdir, 'automation-report.json');
    const report = {
      schemaVersion: 'ae-automation-report/v1',
      generatedAt: '2026-03-04T00:00:00.000Z',
      tool: 'codex-autopilot-lane',
      status: 'resolved',
      run: {
        workflow: 'Codex Autopilot Lane',
        event: 'pull_request',
        runId: 100,
        attempt: 1,
        url: 'https://github.com/itdojp/ae-framework/actions/runs/100',
        repository: 'itdojp/ae-framework',
        ref: 'refs/pull/1/merge',
        sha: 'abc'
      }
    };
    await writeFile(reportPath, JSON.stringify(report));

    const result = spawnSync(process.execPath, [validateScript, reportPath, schemaPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(0);
    expect(result.stderr.toString()).toBe('');
  });

  it('fails for invalid schema version', async () => {
    const reportPath = join(workdir, 'automation-report.json');
    const report = {
      schemaVersion: '1.0.0',
      generatedAt: '2026-03-04T00:00:00.000Z',
      tool: 'codex-autopilot-lane',
      status: 'resolved',
      run: {
        workflow: 'Codex Autopilot Lane',
        event: 'pull_request',
        repository: 'itdojp/ae-framework',
        ref: 'refs/pull/1/merge',
        sha: 'abc'
      }
    };
    await writeFile(reportPath, JSON.stringify(report));

    const result = spawnSync(process.execPath, [validateScript, reportPath, schemaPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('schema validation failed');
  });
});
