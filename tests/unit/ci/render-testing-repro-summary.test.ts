import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { createTempDir, rmrf } from '../../_helpers/tmpfs.js';

function writeJson(filePath: string, payload: unknown): void {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`);
}

describe('render-testing-repro-summary', () => {
  it('aggregates property/replay/mbt summaries into markdown and json', () => {
    const tmpDir = createTempDir('testing-repro-summary-');
    try {
      writeJson(path.join(tmpDir, 'artifacts', 'properties', 'summary.json'), {
        traceId: 'pbt-1',
        seed: 11,
        runs: 5,
        passed: true,
        failed: 0,
        durationMs: 12,
        reproducibleCommand: 'node scripts/testing/property-harness.mjs --seed=11 --runs=5 --focus=pbt-1',
      });
      writeJson(path.join(tmpDir, 'artifacts', 'domain', 'replay.summary.json'), {
        traceId: 'replay-1',
        seed: 0,
        runs: 1,
        passed: 1,
        failed: 0,
        durationMs: 4,
        reproducibleCommand: 'node scripts/testing/replay-runner.mjs --focus=replay-1',
      });
      writeJson(path.join(tmpDir, 'artifacts', 'mbt', 'summary.json'), {
        traceId: 'mbt-1',
        seed: 22,
        runs: 3,
        passed: 3,
        failed: 0,
        durationMs: 8,
        reproducibleCommand: 'node tests/mbt/run.js --seed=22 --runs=3 --depth=3 --trace-id=mbt-1',
      });

      const scriptPath = path.resolve('scripts/ci/render-testing-repro-summary.mjs');
      const result = spawnSync('node', [scriptPath], {
        cwd: tmpDir,
        encoding: 'utf-8',
      });

      expect(result.status).toBe(0);

      const summaryJsonPath = path.join(tmpDir, 'artifacts', 'testing', 'repro-summary.json');
      const summaryMarkdownPath = path.join(tmpDir, 'artifacts', 'testing', 'repro-summary.md');
      expect(fs.existsSync(summaryJsonPath)).toBe(true);
      expect(fs.existsSync(summaryMarkdownPath)).toBe(true);

      const summary = JSON.parse(fs.readFileSync(summaryJsonPath, 'utf-8'));
      expect(Array.isArray(summary.records)).toBe(true);
      expect(summary.records).toHaveLength(3);

      const markdown = fs.readFileSync(summaryMarkdownPath, 'utf-8');
      expect(markdown).toContain('property');
      expect(markdown).toContain('replay');
      expect(markdown).toContain('mbt');
      expect(markdown).toContain('Repro Commands');
    } finally {
      rmrf(tmpDir);
    }
  });
});
