import { describe, it, expect } from 'vitest';
import { mkdtemp, writeFile, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);

const scriptPath = process.env.KVONCE_PROJECTOR_SCRIPT_PATH
  ? resolve(process.cwd(), process.env.KVONCE_PROJECTOR_SCRIPT_PATH)
  : resolve(process.cwd(), 'scripts/trace/projector-kvonce.mjs');

async function withTempDir<T>(fn: (dir: string) => Promise<T>) {
  const dir = await mkdtemp(join(tmpdir(), 'kvonce-projector-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

describe('projector-kvonce CLI', () => {
  it('aggregates events per key and preserves contexts', async () => {
    await withTempDir(async (dir) => {
      const inputPath = join(dir, 'events.ndjson');
      const outputPath = join(dir, 'projection.json');

      const events = [
        { timestamp: '2025-10-04T06:00:00.000Z', type: 'success', key: 'alpha', value: 'v1', context: { attempt: 1 } },
        { timestamp: '2025-10-04T06:00:01.000Z', type: 'retry', key: 'alpha', context: { attempt: 1 } },
        { timestamp: '2025-10-04T06:00:02.000Z', type: 'failure', key: 'alpha', reason: 'duplicate', context: { status: 409 } },
        { timestamp: '2025-10-04T06:01:00.000Z', type: 'success', key: 'beta', value: 'v2' }
      ]
        .map((event) => JSON.stringify(event))
        .join('\n');

      await writeFile(inputPath, events, 'utf8');

      await execFileAsync('node', [scriptPath, '--input', inputPath, '--output', outputPath]);

      const projection = JSON.parse(await readFile(outputPath, 'utf8'));

      expect(projection.eventCount).toBe(4);
      expect(projection.perKey.alpha).toMatchObject({
        successCount: 1,
        retries: 1,
        failureReasons: ['duplicate'],
        value: 'v1',
      });
      expect(projection.perKey.alpha.retryContexts).toEqual([{ attempt: 1 }]);
      expect(projection.perKey.alpha.successContexts).toEqual([{ attempt: 1 }]);
      expect(projection.perKey.alpha.failureContexts).toEqual([{ status: 409 }]);
      expect(projection.perKey.beta).toMatchObject({
        successCount: 1,
        retries: 0,
        failureReasons: [],
        value: 'v2',
      });
      expect(typeof projection.generatedAt).toBe('string');
    });
  });

  it('fails on malformed NDJSON input', async () => {
    await withTempDir(async (dir) => {
      const inputPath = join(dir, 'events.ndjson');
      await writeFile(inputPath, '{"type": "success"}\n{"type":', 'utf8');

      const result = await execFileAsync('node', [scriptPath, '--input', inputPath]).catch((error) => error);
      expect(result.code).not.toBe(0);
      expect(result.stderr).toContain('Invalid JSON on line 2');
    });
  });
});
