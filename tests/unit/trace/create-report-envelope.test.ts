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
    const metadataPath = join(workdir, 'kvonce-payload-metadata.json');
    const extraArtifactPath = join(workdir, 'additional.json');
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
    await writeFile(metadataPath, JSON.stringify({ sha256: 'abc', sizeBytes: 42 }));
    await writeFile(extraArtifactPath, JSON.stringify({ hello: 'world' }));

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
        REPORT_ENVELOPE_NOTES: 'note-one\nnote-two',
        REPORT_ENVELOPE_PAYLOAD_METADATA: metadataPath,
        REPORT_ENVELOPE_EXTRA_ARTIFACTS: extraArtifactPath
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
    expect(envelope.artifacts).toHaveLength(3);
    expect(envelope.artifacts[0]).toMatchObject({
      type: 'application/json',
      path: expect.stringContaining('verify-lite-run-summary.json'),
      checksum: expect.stringMatching(/^sha256:[0-9a-f]{64}$/),
      description: 'Raw summary artifact'
    });
    expect(envelope.artifacts[1]).toMatchObject({
      path: expect.stringContaining('kvonce-payload-metadata.json'),
      description: 'Payload metadata'
    });
    expect(envelope.artifacts[2]).toMatchObject({
      path: expect.stringContaining('additional.json'),
      checksum: expect.stringMatching(/^sha256:[0-9a-f]{64}$/)
    });
    expect(envelope.notes).toEqual(['note-one', 'note-two']);
  });

  it('derives trace ids from the summary when env is empty', async () => {
    const summaryPath = join(workdir, 'summary.json');
    const outputPath = join(workdir, 'envelope.json');

    const summary = {
      schemaVersion: '1.0.0',
      trace: {
        status: 'valid',
        traceIds: ['trace-a', 'trace-b']
      }
    };

    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [scriptPath, summaryPath, outputPath], {
      cwd: workdir,
      env: {
        ...process.env,
        REPORT_ENVELOPE_SOURCE: 'trace-replay',
        GITHUB_RUN_ID: '123',
        GITHUB_WORKFLOW: 'trace-workflow',
        GITHUB_SHA: 'abcdef0',
        GITHUB_REF: 'refs/heads/test-branch'
      }
    });

    expect(result.status).toBe(0);

    const envelope = JSON.parse(await readFile(outputPath, 'utf8'));
    expect(envelope.correlation.traceIds).toEqual(['trace-a', 'trace-b']);
    expect(envelope.summary.trace.traceIds).toEqual(['trace-a', 'trace-b']);
  });
});
