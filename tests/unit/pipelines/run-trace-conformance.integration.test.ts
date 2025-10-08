import { describe, it, expect } from 'vitest';
import { mkdtemp, rm, readFile, mkdir } from 'node:fs/promises';
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
  it('generates a summary and report envelope', async () => {
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
      expect(summary.trace).toBeDefined();

      const envelope = JSON.parse(await readFile(envelopePath, 'utf8'));
      expect(envelope.source).toBe('pipelines:trace');
      expect(envelope.summary.trace.status).toBe(summary.trace.status);
      expect(Array.isArray(envelope.artifacts)).toBe(true);
      expect(envelope.artifacts.length).toBeGreaterThan(0);
    });
  });
});
