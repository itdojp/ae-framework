import { describe, it, expect } from 'vitest';
import { mkdtemp, rm, readFile, mkdir, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);

async function withTempDir<T>(fn: (dir: string) => Promise<T>) {
  const dir = await mkdtemp(join(tmpdir(), 'heavy-thresholds-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

async function runRecommendationScript(args: string[]) {
  const nodePath = process.execPath;
  const scriptPath = resolve('scripts/pipelines/recommend-heavy-trend-thresholds.mjs');
  return execFileAsync(nodePath, [scriptPath, ...args]);
}

describe('recommend-heavy-trend-thresholds', () => {
  it('emits a stable no_data schema when history is missing', async () => {
    await withTempDir(async (dir) => {
      const historyDir = join(dir, 'history');
      const markdownPath = join(dir, 'threshold-recommendation.md');
      const jsonPath = join(dir, 'threshold-recommendation.json');

      await runRecommendationScript([
        '--history-dir',
        historyDir,
        '--markdown-output',
        markdownPath,
        '--json-output',
        jsonPath,
        '--min-snapshots',
        '14',
      ]);

      const output = JSON.parse(await readFile(jsonPath, 'utf8'));
      expect(output.status).toBe('no_data');
      expect(output.snapshotCount).toBe(0);
      expect(output.quantiles).toBeDefined();
      expect(output.currentThresholds).toBeDefined();
      expect(output.sampleCounts.mutationScore).toBe(0);
      expect(output.recommendations.warnMutationScore).toBeNull();

      const markdown = await readFile(markdownPath, 'utf8');
      expect(markdown).toContain('Status: no_data');
      expect(markdown).toContain('No snapshots found.');
    });
  });

  it('keeps mutation delta recommendations at or below zero', async () => {
    await withTempDir(async (dir) => {
      const historyDir = join(dir, 'history');
      const markdownPath = join(dir, 'threshold-recommendation.md');
      const jsonPath = join(dir, 'threshold-recommendation.json');
      await mkdir(historyDir, { recursive: true });

      await writeFile(
        join(historyDir, '2026-02-01T00-00-00Z.json'),
        JSON.stringify({
          entries: [
            {
              label: 'Mutation quick',
              metrics: {
                mutationScore: { current: 99.1, delta: 0.8 },
              },
            },
          ],
        }),
      );
      await writeFile(
        join(historyDir, '2026-02-02T00-00-00Z.json'),
        JSON.stringify({
          entries: [
            {
              label: 'Mutation quick',
              metrics: {
                mutationScore: { current: 99.0, delta: 0.3 },
              },
            },
          ],
        }),
      );

      await runRecommendationScript([
        '--history-dir',
        historyDir,
        '--markdown-output',
        markdownPath,
        '--json-output',
        jsonPath,
        '--min-snapshots',
        '2',
      ]);

      const output = JSON.parse(await readFile(jsonPath, 'utf8'));
      expect(output.status).toBe('ready');
      expect(output.recommendations.warnMutationDelta).toBeLessThanOrEqual(0);
      expect(output.recommendations.criticalMutationDelta).toBeLessThanOrEqual(0);
    });
  });

  it('accepts current-threshold overrides from CLI options', async () => {
    await withTempDir(async (dir) => {
      const historyDir = join(dir, 'history');
      const markdownPath = join(dir, 'threshold-recommendation.md');
      const jsonPath = join(dir, 'threshold-recommendation.json');
      await mkdir(historyDir, { recursive: true });

      await writeFile(
        join(historyDir, '2026-02-01T00-00-00Z.json'),
        JSON.stringify({
          entries: [
            {
              label: 'Mutation quick',
              metrics: {
                mutationScore: { current: 97.9, delta: -0.8 },
              },
            },
          ],
        }),
      );

      await runRecommendationScript([
        '--history-dir',
        historyDir,
        '--markdown-output',
        markdownPath,
        '--json-output',
        jsonPath,
        '--warn-mutation-score',
        '97',
        '--critical-mutation-score',
        '95',
        '--warn-property-failed',
        '2',
        '--critical-property-failed',
        '4',
        '--min-snapshots',
        '1',
      ]);

      const output = JSON.parse(await readFile(jsonPath, 'utf8'));
      expect(output.currentThresholds.warnMutationScore).toBe(97);
      expect(output.currentThresholds.criticalMutationScore).toBe(95);
      expect(output.currentThresholds.warnPropertyFailed).toBe(2);
      expect(output.currentThresholds.criticalPropertyFailed).toBe(4);
    });
  });
});
