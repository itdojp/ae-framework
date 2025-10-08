import { describe, it, expect } from 'vitest';
import { mkdtemp, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);
const scriptPath = resolve('scripts/trace/projector-kvonce.mjs');

async function withTempDir<T>(fn: (dir: string) => Promise<T>) {
  const dir = await mkdtemp(join(tmpdir(), 'projector-kvonce-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

describe('projector-kvonce CLI', () => {
  it('produces stats for the sample NDJSON input', async () => {
    const result = await execFileAsync(process.execPath, [
      scriptPath,
      '--input',
      'samples/trace/kvonce-sample.ndjson',
    ]);

    const projection = JSON.parse(result.stdout);
    expect(projection.eventCount).toBe(4);
    expect(projection.stats).toEqual(
      expect.objectContaining({
        totalEvents: 4,
        uniqueKeys: 2,
        successRate: 0.5,
      }),
    );
    expect(projection.stats.byType).toEqual(
      expect.objectContaining({ success: 2, retry: 1, failure: 1, unknown: 0 }),
    );
    expect(projection.stats.keysWithFailures).toBe(1);
    expect(Array.isArray(projection.stateSequence)).toBe(true);
    expect(projection.stateSequence.length).toBe(4);
  });

  it('writes the state sequence to a dedicated file when requested', async () => {
    await withTempDir(async (dir) => {
      const outputPath = join(dir, 'projection.json');
      const statePath = join(dir, 'projected', 'kvonce-state-sequence.json');

      await execFileAsync(process.execPath, [
        scriptPath,
        '--input',
        'samples/trace/kvonce-sample.ndjson',
        '--output',
        outputPath,
        '--state-output',
        statePath,
      ]);

      const projection = JSON.parse(await readFile(outputPath, 'utf8'));
      expect(projection.outputs?.stateSequence).toBeDefined();
      const stateSequence = JSON.parse(await readFile(statePath, 'utf8'));
      expect(Array.isArray(stateSequence)).toBe(true);
      expect(stateSequence.length).toBe(projection.stats?.stateSequenceLength ?? projection.eventCount);
    });
  });
});
