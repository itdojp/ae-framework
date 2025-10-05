import { describe, it, expect } from 'vitest';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);
const scriptPath = process.env.KVONCE_CONFORMANCE_SCRIPT_PATH
  ? resolve(process.cwd(), process.env.KVONCE_CONFORMANCE_SCRIPT_PATH)
  : resolve(process.cwd(), 'scripts/trace/run-kvonce-conformance.sh');

async function withTempDir<T>(fn: (dir: string) => Promise<T>) {
  const dir = await mkdtemp(join(tmpdir(), 'kvonce-conformance-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

describe('run-kvonce-conformance.sh', () => {
  it('produces projection and validation for NDJSON sample', async () => {
    await withTempDir(async (dir) => {
      const outputDir = join(dir, 'ndjson');
      await execFileAsync('bash', [scriptPath, '--input', 'samples/trace/kvonce-sample.ndjson', '--format', 'ndjson', '--output-dir', outputDir]);

      const projection = JSON.parse(await readFile(join(outputDir, 'kvonce-projection.json'), 'utf8'));
      const validation = JSON.parse(await readFile(join(outputDir, 'kvonce-validation.json'), 'utf8'));

      expect(validation.valid).toBe(true);
      expect(projection.eventCount).toBeGreaterThan(0);
      expect(Object.keys(projection.perKey)).toContain('alpha');
    });
  });

  it('converts OTLP payload and validates it', async () => {
    await withTempDir(async (dir) => {
      const payload = resolve('samples/trace/kvonce-otlp.json');
      const outputDir = join(dir, 'otlp');
      await execFileAsync('bash', [scriptPath, '--input', payload, '--format', 'otlp', '--output-dir', outputDir]);

      const validation = JSON.parse(await readFile(join(outputDir, 'kvonce-validation.json'), 'utf8'));
      expect(validation.valid).toBe(true);
    });
  });

  it('fails when validation reports issues', async () => {
    await withTempDir(async (dir) => {
      const invalid = join(dir, 'invalid.ndjson');
      const lines = [
        JSON.stringify({ type: 'success', key: 'alpha', value: 'v1' }),
        JSON.stringify({ type: 'success', key: 'alpha', value: 'v2' }),
      ].join('\n');
      await writeFile(invalid, lines, 'utf8');

      const result = await execFileAsync('bash', [scriptPath, '--input', invalid, '--format', 'ndjson', '--output-dir', join(dir, 'out')]).catch((error) => error);
      expect(result.code).not.toBe(0);
    });
  });
});
