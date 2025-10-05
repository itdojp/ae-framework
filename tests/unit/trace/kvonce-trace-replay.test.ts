import { describe, it, expect } from 'vitest';
import { mkdtemp, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);
const scriptPath = resolve(__dirname, '../../../scripts/trace/run-kvonce-trace-replay.mjs');

async function withTempDir(fn: (dir: string) => Promise<void>) {
  const dir = await mkdtemp(join(tmpdir(), 'kvonce-replay-'));
  try {
    await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

describe('run-kvonce-trace-replay.mjs', () => {
  it('produces replay summary from sample trace', async () => {
    await withTempDir(async (dir) => {
      const outputDir = join(dir, 'replay');
      const result = await execFileAsync('node', [
        scriptPath,
        '--input',
        'samples/trace/kvonce-sample.ndjson',
        '--format',
        'ndjson',
        '--output-dir',
        outputDir,
      ]);
      expect(result.stdout).toContain('KvOnce trace replay summary');
      const summaryPath = join(outputDir, 'kvonce-trace-replay.json');
      const summary = JSON.parse(await readFile(summaryPath, 'utf8'));
      expect(summary.input).toBe('samples/trace/kvonce-sample.ndjson');
      expect(summary.conformance.status).toBe('ran');
      expect(summary.conformance.report?.valid).toBe(true);
      expect(typeof summary.tlc.status).toBe('string');
    });
  });
});
