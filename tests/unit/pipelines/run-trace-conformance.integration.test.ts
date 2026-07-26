import { describe, it, expect } from 'vitest';
import { mkdtemp, rm, readFile, mkdir, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);

async function withTempDir<T>(fn: (dir: string) => Promise<T>) {
  const dir = await mkdtemp(join(tmpdir(), 'pipelines-trace-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

describe('pipelines:trace', () => {
  it('generates a summary and report envelope', { timeout: 20_000 }, async () => {
    await withTempDir(async (dir) => {
      const nodePath = process.execPath;
      const scriptPath = resolve('scripts/pipelines/run-trace-conformance.mjs');
      const traceOutputDir = join(dir, 'trace-output');
      const summaryPath = join(dir, 'conformance-summary.json');
      const envelopePath = join(dir, 'trace-envelope.json');

      await mkdir(traceOutputDir, { recursive: true });

      await execFileAsync(nodePath, [
        scriptPath,
        '--input',
        'samples/trace/kvonce-sample.ndjson',
        '--format',
        'ndjson',
        '--output-dir',
        traceOutputDir,
        '--summary-out',
        summaryPath,
        '--envelope-out',
        envelopePath,
        '--skip-replay',
      ]);

      const summary = JSON.parse(await readFile(summaryPath, 'utf8'));
      expect(summary.schemaVersion).toBe('verify-profile-summary/v1');
      expect(summary.profile).toBe('conformance');
      expect(summary.overall_status).toBe('pass');
      expect(Array.isArray(summary.steps)).toBe(true);
      expect(summary.steps[0]?.name).toBe('verify:conformance');
      expect(summary.steps[0]?.status).toBe('passed');

      const envelope = JSON.parse(await readFile(envelopePath, 'utf8'));
      expect(envelope.source).toBe('pipelines:trace');
      expect(envelope.summary.profile).toBe(summary.profile);
      expect(envelope.summary.overall_status).toBe(summary.overall_status);
      expect(Array.isArray(envelope.artifacts)).toBe(true);
      expect(envelope.artifacts.length).toBeGreaterThan(0);
    });
  });

  it('executes a pnpm JavaScript entrypoint through the current Node runtime', async () => {
    await withTempDir(async (dir) => {
      const scriptPath = resolve('scripts/pipelines/run-trace-conformance.mjs');
      const fakePnpm = join(dir, 'pnpm.cjs');
      const recordPath = join(dir, 'pnpm-args.json');
      await writeFile(fakePnpm, `
const fs = require('node:fs');
fs.writeFileSync(process.env.FAKE_PNPM_RECORD, JSON.stringify(process.argv.slice(2)));
`, 'utf8');

      await execFileAsync(process.execPath, [
        scriptPath,
        '--input',
        'samples/trace/kvonce-sample.ndjson',
        '--output-dir',
        join(dir, 'trace-output'),
        '--summary-out',
        join(dir, 'conformance-summary.json'),
        '--skip-replay',
        '--no-envelope',
      ], {
        env: {
          ...process.env,
          npm_execpath: fakePnpm,
          FAKE_PNPM_RECORD: recordPath,
        },
      });

      expect(JSON.parse(await readFile(recordPath, 'utf8'))).toEqual([
        'verify:conformance',
        '--trace',
        'samples/trace/kvonce-sample.ndjson',
        '--trace-format',
        'auto',
        '--trace-output',
        expect.any(String),
        '--out',
        expect.any(String),
        '--trace-skip-replay',
      ]);
    });
  });

  it('fails deterministically when the pnpm process cannot start', async () => {
    await withTempDir(async (dir) => {
      const scriptPath = resolve('scripts/pipelines/run-trace-conformance.mjs');

      await expect(execFileAsync(process.execPath, [
        scriptPath,
        '--input',
        'samples/trace/kvonce-sample.ndjson',
        '--output-dir',
        join(dir, 'trace-output'),
        '--summary-out',
        join(dir, 'conformance-summary.json'),
        '--skip-replay',
        '--no-envelope',
      ], {
        env: {
          ...process.env,
          PATH: '',
          npm_execpath: '',
        },
      })).rejects.toMatchObject({
        code: 1,
        stderr: expect.stringContaining('[pipelines:trace] failed to start pnpm:'),
      });
    });
  });
});
