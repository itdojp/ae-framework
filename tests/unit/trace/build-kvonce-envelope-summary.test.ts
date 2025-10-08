import { describe, it, expect } from 'vitest';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);
const projectorScript = resolve('scripts/trace/projector-kvonce.mjs');
const validatorScript = resolve('scripts/trace/validate-kvonce.mjs');
const summaryScript = resolve('scripts/trace/build-kvonce-envelope-summary.mjs');

async function withTempDir<T>(fn: (dir: string) => Promise<T>) {
  const dir = await mkdtemp(join(tmpdir(), 'kvonce-envelope-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

describe('build-kvonce-envelope-summary', () => {
  it('collects current run artifacts and attaches conformance summary', async () => {
    await withTempDir(async (dir) => {
      const traceDir = join(dir, 'trace');
      const projectionPath = join(traceDir, 'kvonce-projection.json');
      const validationPath = join(traceDir, 'kvonce-validation.json');
      const stateSequencePath = join(traceDir, 'projected', 'kvonce-state-sequence.json');
      const conformanceSummaryPath = join(traceDir, 'kvonce-conformance-summary.json');
      const outputPath = join(dir, 'kvonce-trace-summary.json');

      await execFileAsync(process.execPath, [
        projectorScript,
        '--input',
        'samples/trace/kvonce-sample.ndjson',
        '--output',
        projectionPath,
        '--state-output',
        stateSequencePath,
      ]);

      await execFileAsync(process.execPath, [
        validatorScript,
        '--input',
        projectionPath,
        '--output',
        validationPath,
      ]);

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

      await execFileAsync(process.execPath, [
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
      expect(currentCase.valid).toBe(true);
      expect(currentCase.projectionPath).toMatch(/kvonce-projection\.json$/);
      expect(currentCase.validationPath).toMatch(/kvonce-validation\.json$/);
      expect(summary.traceIds).toContain('trace-xyz');
      expect(summary.tempoLinks).toContain('https://tempo.example.com/explore?traceId=trace-xyz');
    });
  });
});
