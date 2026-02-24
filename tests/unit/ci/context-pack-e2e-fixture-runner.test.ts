import { describe, expect, it, afterEach } from 'vitest';
import { cp, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const runnerScript = resolve(repoRoot, 'scripts/context-pack/run-e2e-fixture.mjs');
const baseFixtureDir = resolve(repoRoot, 'fixtures/context-pack/e2e');

const reportDirs: string[] = [];
const fixtureDirs: string[] = [];

afterEach(async () => {
  await Promise.all(
    reportDirs.splice(0).map((dirPath) => rm(dirPath, { recursive: true, force: true })),
  );
  await Promise.all(
    fixtureDirs.splice(0).map((dirPath) => rm(dirPath, { recursive: true, force: true })),
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

  it('keeps failure reports and marks keepReports=true when validation fails', async () => {
    const fixtureDir = await mkdtemp(join(tmpdir(), 'context-pack-e2e-fixture-broken-'));
    fixtureDirs.push(fixtureDir);
    await cp(baseFixtureDir, fixtureDir, { recursive: true });

    const phase5Path = join(fixtureDir, 'phase5-templates.json');
    const phase5Payload = JSON.parse(await readFile(phase5Path, 'utf8')) as {
      pullbacks: Array<{ leftMorphismId: string }>;
    };
    phase5Payload.pullbacks[0].leftMorphismId = 'MissingMorphism';
    await writeFile(phase5Path, `${JSON.stringify(phase5Payload, null, 2)}\n`, 'utf8');

    const result = spawnSync(
      process.execPath,
      [runnerScript, '--fixture-dir', fixtureDir],
      {
        cwd: repoRoot,
        encoding: 'utf8',
      },
    );

    expect(result.status).toBe(2);

    const reportDirMatch = result.stdout.match(/report dir: (.+)\n/);
    expect(reportDirMatch).not.toBeNull();
    const reportDir = resolve(repoRoot, reportDirMatch?.[1] ?? '');
    reportDirs.push(reportDir);

    const summaryPath = join(reportDir, 'context-pack-e2e-summary.json');
    expect(existsSync(summaryPath)).toBe(true);

    const summary = JSON.parse(await readFile(summaryPath, 'utf8')) as {
      status: string;
      keepReports: boolean;
      steps: Array<{ name: string; exitCode: number }>;
    };

    expect(summary.status).toBe('fail');
    expect(summary.keepReports).toBe(true);
    expect(summary.steps.some((step) => step.exitCode !== 0)).toBe(true);
  });
});
