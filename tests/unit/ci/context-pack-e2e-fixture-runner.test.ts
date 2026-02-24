import { describe, expect, it, afterEach } from 'vitest';
import { mkdtemp, readFile, rm } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const runnerScript = resolve(repoRoot, 'scripts/context-pack/run-e2e-fixture.mjs');

const reportDirs: string[] = [];

afterEach(async () => {
  await Promise.all(
    reportDirs.splice(0).map((dirPath) => rm(dirPath, { recursive: true, force: true })),
  );
});

describe('context-pack fixture e2e runner', () => {
  it('runs full context-pack validation sequence with fixture', async () => {
    const reportDir = await mkdtemp(join(tmpdir(), 'context-pack-e2e-report-'));
    reportDirs.push(reportDir);

    const result = spawnSync(
      process.execPath,
      [runnerScript, '--report-dir', reportDir],
      {
        cwd: repoRoot,
      },
    );

    expect(result.status).toBe(0);

    const summaryPath = join(reportDir, 'context-pack-e2e-summary.json');
    expect(existsSync(summaryPath)).toBe(true);

    const summary = JSON.parse(await readFile(summaryPath, 'utf8')) as {
      status: string;
      steps: Array<{ name: string; exitCode: number }>;
    };

    expect(summary.status).toBe('pass');
    expect(summary.steps).toHaveLength(5);
    for (const step of summary.steps) {
      expect(step.exitCode).toBe(0);
    }

    expect(existsSync(join(reportDir, 'context-pack-validate-report.json'))).toBe(true);
    expect(existsSync(join(reportDir, 'context-pack-phase5-report.json'))).toBe(true);
  });
});
