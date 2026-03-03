import { describe, it, expect } from 'vitest';
import { mkdtemp, readdir, readFile, rm, writeFile } from 'node:fs/promises';
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

async function listArtifacts(rootDir: string, current = ''): Promise<string[]> {
  const absolute = current ? join(rootDir, current) : rootDir;
  const entries = await readdir(absolute, { withFileTypes: true });
  const files: string[] = [];
  for (const entry of entries) {
    const rel = current ? join(current, entry.name) : entry.name;
    if (entry.isDirectory()) {
      files.push(...(await listArtifacts(rootDir, rel)));
      continue;
    }
    if (entry.isFile()) {
      files.push(rel.replaceAll('\\', '/'));
    }
  }
  return files.sort();
}

describe('run-kvonce-conformance.sh', () => {
  it('produces projection and validation for NDJSON sample', async () => {
    await withTempDir(async (dir) => {
      const outputDir = join(dir, 'ndjson');
      await execFileAsync('bash', [scriptPath, '--input', 'samples/trace/kvonce-sample.ndjson', '--format', 'ndjson', '--output-dir', outputDir]);

      const projection = JSON.parse(await readFile(join(outputDir, 'kvonce-projection.json'), 'utf8'));
      const stateSequencePath = projection.outputs?.stateSequence
        ? resolve(process.cwd(), projection.outputs.stateSequence)
        : join(outputDir, 'projected/kvonce-state-sequence.json');
      const stateSequence = JSON.parse(await readFile(stateSequencePath, 'utf8'));
      const validation = JSON.parse(await readFile(join(outputDir, 'kvonce-validation.json'), 'utf8'));

      expect(validation.valid).toBe(true);
      expect(projection.eventCount).toBeGreaterThan(0);
      expect(Object.keys(projection.perKey)).toContain('alpha');
      expect(projection.stats).toBeDefined();
      expect(Array.isArray(stateSequence)).toBe(true);
      expect(stateSequence.length).toBe(projection.stats?.stateSequenceLength ?? projection.eventCount);
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

  it('emits the same artifact set for NDJSON and OTLP paths', async () => {
    await withTempDir(async (dir) => {
      const ndjsonOutputDir = join(dir, 'ndjson');
      const otlpOutputDir = join(dir, 'otlp');
      await execFileAsync('bash', [scriptPath, '--input', 'samples/trace/kvonce-sample.ndjson', '--format', 'ndjson', '--output-dir', ndjsonOutputDir]);
      await execFileAsync('bash', [scriptPath, '--input', 'samples/trace/kvonce-otlp.json', '--format', 'otlp', '--output-dir', otlpOutputDir]);

      const ndjsonArtifacts = await listArtifacts(ndjsonOutputDir);
      const otlpArtifacts = await listArtifacts(otlpOutputDir);

      expect(ndjsonArtifacts).toEqual([
        'kvonce-events.ndjson',
        'kvonce-projection.json',
        'kvonce-validation.json',
        'projected/kvonce-state-sequence.json',
      ]);
      expect(otlpArtifacts).toEqual(ndjsonArtifacts);
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
