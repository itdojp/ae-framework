import { afterEach, describe, expect, it } from 'vitest';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const suggestScript = resolve(repoRoot, 'scripts/context-pack/suggest.mjs');
const workdirs: string[] = [];

async function createWorkdir(prefix: string): Promise<string> {
  const workdir = await mkdtemp(join(tmpdir(), prefix));
  workdirs.push(workdir);
  return workdir;
}

async function writeJson(filePath: string, payload: unknown): Promise<void> {
  await mkdir(dirname(filePath), { recursive: true });
  await writeFile(filePath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
}

afterEach(async () => {
  await Promise.all(workdirs.splice(0).map((workdir) => rm(workdir, { recursive: true, force: true })));
});

describe('context-pack suggestion generator', () => {
  it('builds recommendedContextChanges from context-pack report violations', async () => {
    const workdir = await createWorkdir('context-pack-suggest-');
    const reportDir = join(workdir, 'artifacts', 'context-pack');
    await mkdir(reportDir, { recursive: true });

    await writeJson(join(reportDir, 'context-pack-functor-report.json'), {
      schemaVersion: 'context-pack-functor-report/v1',
      status: 'fail',
      violations: [
        {
          type: 'morphism-mapping-missing',
          severity: 'error',
          morphismId: 'ReserveInventory',
          message: "Morphism mapping is missing for 'ReserveInventory'",
        },
      ],
    });
    await writeJson(join(reportDir, 'deps-summary.json'), {
      schemaVersion: 'context-pack-deps-summary/v1',
      status: 'warn',
      violations: [
        {
          type: 'boundary-violation',
          severity: 'error',
          ruleId: 'core-does-not-depend-on-agents',
          from: 'src/core/service.ts',
          to: 'src/agents/runner.ts',
          reason: 'Core layer must stay independent. See C:\\agents\\runner.ts',
        },
      ],
    });

    const result = spawnSync(process.execPath, [suggestScript, '--report-dir', reportDir], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);
    expect(existsSync(join(reportDir, 'context-pack-suggestions.json'))).toBe(true);
    expect(existsSync(join(reportDir, 'context-pack-suggestions.md'))).toBe(true);

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-suggestions.json'), 'utf8')) as {
      status: string;
      summary: {
        totalSuggestions: number;
      };
      recommendedContextChanges: Array<{
        source: string;
        changeType: string;
        file: string;
        suggestedCommand: string;
      }>;
    };

    expect(report.status).toBe('fail');
    expect(report.summary.totalSuggestions).toBeGreaterThanOrEqual(2);
    expect(
      report.recommendedContextChanges.some(
        (entry) =>
          entry.source === 'functor'
          && entry.changeType === 'add'
          && entry.file === 'spec/context-pack/functor-map.json'
          && entry.suggestedCommand === 'pnpm run context-pack:verify-functor',
      ),
    ).toBe(true);
    expect(
      report.recommendedContextChanges.some(
        (entry) =>
          entry.source === 'deps'
          && entry.changeType === 'investigate'
          && entry.file === 'src/core/service.ts'
          && entry.suggestedCommand === 'pnpm run context-pack:deps -- --strict=true',
      ),
    ).toBe(true);

    const markdown = await readFile(join(reportDir, 'context-pack-suggestions.md'), 'utf8');
    expect(markdown).toContain('C:\\\\agents\\\\runner.ts');
  });

  it('returns pass when no input report is present', async () => {
    const workdir = await createWorkdir('context-pack-suggest-empty-');
    const reportDir = join(workdir, 'artifacts', 'context-pack');
    await mkdir(reportDir, { recursive: true });

    const result = spawnSync(process.execPath, [suggestScript, '--report-dir', reportDir], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-suggestions.json'), 'utf8')) as {
      status: string;
      summary: {
        scannedReports: number;
        missingReports: number;
        totalSuggestions: number;
      };
    };

    expect(report.status).toBe('pass');
    expect(report.summary.scannedReports).toBe(6);
    expect(report.summary.missingReports).toBe(6);
    expect(report.summary.totalSuggestions).toBe(0);
  });
});
