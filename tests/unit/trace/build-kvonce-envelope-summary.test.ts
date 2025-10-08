import { describe, it, expect } from 'vitest';
import { mkdtemp, rm, writeFile, readFile, mkdir } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);

async function withTempDir<T>(fn: (dir: string) => Promise<T>) {
  const dir = await mkdtemp(join(tmpdir(), 'kvonce-summary-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

describe('build-kvonce-envelope-summary.mjs', () => {
  it('collects trace ids and conformance summary', async () => {
    await withTempDir(async (dir) => {
      const nodePath = process.execPath;
      const projectorScript = resolve('scripts/trace/projector-kvonce.mjs');
      const validatorScript = resolve('scripts/trace/validate-kvonce.mjs');
      const summaryScript = resolve('scripts/trace/build-kvonce-envelope-summary.mjs');

      const traceDir = join(dir, 'trace');
      await mkdir(join(traceDir, 'projected'), { recursive: true });

      const ndjsonPath = join(dir, 'input.ndjson');
      const events = [
        { traceId: 'trace-123', timestamp: '2025-10-08T10:00:00.000Z', type: 'success', key: 'alpha', value: 'v1' },
        { traceId: 'trace-123', timestamp: '2025-10-08T10:01:00.000Z', type: 'retry', key: 'alpha', context: { attempts: 1 } },
      ]
        .map((event) => JSON.stringify(event))
        .join('\n');
      await writeFile(ndjsonPath, events, 'utf8');
      await writeFile(join(traceDir, 'kvonce-events.ndjson'), events, 'utf8');

      const projectionPath = join(traceDir, 'kvonce-projection.json');
      const stateSequencePath = join(traceDir, 'projected', 'kvonce-state-sequence.json');
      await execFileAsync(nodePath, [
        projectorScript,
        '--input',
        ndjsonPath,
        '--output',
        projectionPath,
        '--state-output',
        stateSequencePath,
      ]);

      const validationPath = join(traceDir, 'kvonce-validation.json');
      await execFileAsync(nodePath, [
        validatorScript,
        '--input',
        projectionPath,
        '--output',
        validationPath,
      ]);

      const conformanceSummaryPath = join(traceDir, 'kvonce-conformance-summary.json');
      const conformanceSummary = {
        trace: {
          status: 'valid',
          traceIds: ['trace-123'],
        },
      };
      await writeFile(conformanceSummaryPath, JSON.stringify(conformanceSummary, null, 2));

      const outputPath = join(dir, 'kvonce-trace-summary.json');
      await execFileAsync(nodePath, [
        summaryScript,
        '--trace-dir',
        traceDir,
        '--summary',
        conformanceSummaryPath,
        '--output',
        outputPath,
      ]);

      const summary = JSON.parse(await readFile(outputPath, 'utf8'));
      expect(summary.traceIds).toEqual(['trace-123']);
      const currentCase = summary.cases.find((entry) => entry.format === 'current');
      expect(currentCase?.traceIds).toEqual(['trace-123']);
      expect(currentCase?.projectionPath).toBeDefined();
      expect(summary.conformance.trace.traceIds).toEqual(['trace-123']);
    });
  });
});
