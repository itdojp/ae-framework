import { describe, it, expect } from 'vitest';
import { mkdtemp, readFile, rm, writeFile, mkdir } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);
const projectorScript = resolve('scripts/trace/projector-kvonce.mjs');
const validatorScript = resolve('scripts/trace/validate-kvonce.mjs');
const summaryScript = resolve('scripts/trace/build-kvonce-envelope-summary.mjs');

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
      const traceDir = join(dir, 'trace');
      await mkdir(join(traceDir, 'projected'), { recursive: true });

      const ndjsonPath = join(traceDir, 'kvonce-events.ndjson');
      const events = [
        { traceId: 'trace-xyz', timestamp: '2025-10-08T10:00:00.000Z', type: 'success', key: 'alpha', value: 'v1' },
        { traceId: 'trace-xyz', timestamp: '2025-10-08T10:01:00.000Z', type: 'retry', key: 'alpha', context: { attempts: 1 } },
      ]
        .map((event) => JSON.stringify(event))
        .join('\n');
      await writeFile(ndjsonPath, events, 'utf8');

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
          projection: {
            path: projectionPath,
            events: 4,
          },
          validation: {
            path: validationPath,
            issues: 0,
            valid: true,
          },
          traceIds: ['trace-xyz'],
        },
        tempoLinks: ['https://tempo.example.com/explore?traceId=trace-xyz'],
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
      expect(summary.conformance?.trace?.status).toBe('valid');
      const currentCase = summary.cases.find((entry: { format: string }) => entry.format === 'current');
      expect(currentCase).toBeDefined();
      expect(currentCase?.valid).toBe(true);
      expect(currentCase?.projectionPath).toMatch(/kvonce-projection\.json$/);
      expect(currentCase?.validationPath).toMatch(/kvonce-validation\.json$/);
      expect(currentCase?.traceIds).toEqual(['trace-xyz']);
      expect(summary.traceIds).toEqual(['trace-xyz']);
      expect(summary.tempoLinks).toContain('https://tempo.example.com/explore?traceId=trace-xyz');
      expect(summary.conformance?.trace?.traceIds).toEqual(['trace-xyz']);
      expect(summary.trace?.traceIds).toEqual(['trace-xyz']);
      expect(summary.trace?.tempoLinks).toEqual(['https://tempo.example.com/explore?traceId=trace-xyz']);
      const domain = summary.trace?.domains?.find((entry: { key: string }) => entry.key === 'current');
      expect(domain).toBeDefined();
      expect(domain?.status).toBe('valid');
      expect(domain?.traceIds).toEqual(['trace-xyz']);
      expect(summary.trace?.aggregate?.traceIds).toEqual(['trace-xyz']);
      expect(summary.trace?.aggregate?.tempoLinks).toEqual(['https://tempo.example.com/explore?traceId=trace-xyz']);
      expect(summary.trace?.aggregate?.issues).toBe(0);
    });
  });
});
