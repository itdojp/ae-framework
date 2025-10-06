import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdtemp, rm, writeFile, readFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const scriptPath = join(process.cwd(), 'scripts/trace/create-report-envelope.mjs');

describe('create-report-envelope CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'report-envelope-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('generates an envelope with correlation, artifacts, and notes', async () => {
    const summaryPath = join(workdir, 'verify-lite-run-summary.json');
    const outputPath = join(workdir, 'report-envelope.json');

    const summary = {
      schemaVersion: '1.0.0',
      timestamp: '2025-10-06T02:29:59.000Z',
      flags: {
        install: '--frozen-lockfile',
        noFrozen: false,
        keepLintLog: true,
        enforceLint: true,
        runMutation: true
      },
      steps: {
        install: { status: 'success' },
        lint: { status: 'failure', notes: 'baseline +5' }
      }
    };

    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [scriptPath, summaryPath, outputPath], {
      cwd: workdir,
      env: {
        ...process.env,
        REPORT_ENVELOPE_SOURCE: 'verify-lite',
        GITHUB_RUN_ID: '18268371063',
        GITHUB_WORKFLOW: 'Verify Lite',
        GITHUB_SHA: '01a5c13d',
        GITHUB_REF: 'refs/heads/main',
        REPORT_ENVELOPE_TRACE_IDS: 'trace-1,trace-2',
        REPORT_ENVELOPE_NOTES: 'note-one\nnote-two'
      }
    });

    expect(result.status).toBe(0);
    expect(result.error).toBeUndefined();

    const envelopeRaw = await readFile(outputPath, 'utf8');
    const envelope = JSON.parse(envelopeRaw);

    expect(envelope.schemaVersion).toBe('1.0.0');
    expect(envelope.source).toBe('verify-lite');
    expect(envelope.correlation).toEqual({
      runId: '18268371063',
      workflow: 'Verify Lite',
      commit: '01a5c13d',
      branch: 'refs/heads/main',
      traceIds: ['trace-1', 'trace-2']
    });
    expect(envelope.summary).toEqual(summary);
    expect(envelope.artifacts).toHaveLength(1);
    expect(envelope.artifacts[0]).toMatchObject({
      type: 'application/json',
      path: expect.stringContaining('verify-lite-run-summary.json'),
      checksum: expect.stringMatching(/^sha256:[0-9a-f]{64}$/)
    });
    expect(envelope.notes).toEqual(['note-one', 'note-two']);
  });
});
