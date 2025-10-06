import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdtemp, rm, writeFile, readFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const validateScript = join(process.cwd(), 'scripts/ci/validate-report-envelope.mjs');
const createEnvelope = join(process.cwd(), 'scripts/trace/create-report-envelope.mjs');
const schemaPath = join(process.cwd(), 'schema/report-envelope.schema.json');

describe('validate-report-envelope CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'report-envelope-validate-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('accepts a valid envelope', async () => {
    const summaryPath = join(workdir, 'summary.json');
    const envelopePath = join(workdir, 'envelope.json');

    const summary = {
      schemaVersion: '1.0.0',
      payload: 'example'
    };

    await writeFile(summaryPath, JSON.stringify(summary));

    const createResult = spawnSync(process.execPath, [createEnvelope, summaryPath, envelopePath], {
      cwd: workdir,
      env: {
        ...process.env,
        REPORT_ENVELOPE_SOURCE: 'unit-test',
        GITHUB_RUN_ID: 'run-123',
        GITHUB_WORKFLOW: 'validate-report-envelope-test',
        GITHUB_SHA: 'abc1234',
        GITHUB_REF: 'refs/heads/test'
      }
    });

    expect(createResult.status).toBe(0);
    const envelope = JSON.parse(await readFile(envelopePath, 'utf8'));
    expect(envelope.source).toBe('unit-test');

    const validateResult = spawnSync(process.execPath, [validateScript, envelopePath, schemaPath], {
      cwd: workdir
    });

    expect(validateResult.status).toBe(0);
    expect(validateResult.stderr.toString()).toBe('');
  });

  it('skips when envelope file is absent', () => {
    const validateResult = spawnSync(process.execPath, [validateScript, 'missing.json', schemaPath], {
      cwd: workdir
    });

    expect(validateResult.status).toBe(0);
    expect(validateResult.stderr.toString()).toContain('skipping');
  });
});
