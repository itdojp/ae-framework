import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const triageScript = resolve(repoRoot, 'scripts/maintenance/remote-branch-triage.mjs');
const triageModuleUrl = pathToFileURL(triageScript).href;

describe.sequential('remote-branch-triage script', () => {
  it('builds a structured report from branch inventory JSON', async () => {
    const mod = await import(triageModuleUrl);
    const report = mod.buildTriageReport(
      {
        generatedAt: '2026-03-06T10:00:00Z',
        base: 'origin/main',
        remote: 'origin',
        candidates: {
          remoteMerged: ['feat/merged-a'],
          remoteStaleByAge: [{ branch: 'feat/stale-a', ageDays: 120 }],
        },
      },
      {
        generatedAt: '2026-03-06T11:00:00Z',
        inputJsonPath: 'tmp/maintenance/branch-inventory.json',
      },
    );

    expect(report.summary).toEqual({
      remoteMergedCandidates: 1,
      remoteStaleCandidates: 1,
    });
    expect(report.remoteMerged).toEqual([
      expect.objectContaining({ branch: 'feat/merged-a', proposedAction: 'delete', approval: 'required' }),
    ]);
    expect(report.remoteStale).toEqual([
      expect.objectContaining({ branch: 'feat/stale-a', ageDays: 120, proposedAction: 'review' }),
    ]);
    expect(report.sourceInventory.path).toBe('tmp/maintenance/branch-inventory.json');
  });

  it('writes markdown and json outputs', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-branch-triage-'));
    const inputJson = join(sandbox, 'branch-inventory.json');
    const outputJson = join(sandbox, 'remote-branch-triage.json');
    const outputMd = join(sandbox, 'remote-branch-triage.md');

    try {
      mkdirSync(sandbox, { recursive: true });
      writeFileSync(
        inputJson,
        `${JSON.stringify(
          {
            generatedAt: '2026-03-06T10:00:00Z',
            base: 'origin/main',
            remote: 'origin',
            candidates: {
              remoteMerged: ['feat/merged-a'],
              remoteStaleByAge: [{ branch: 'feat/stale-a', ageDays: 120 }],
            },
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync(
        'node',
        [triageScript, '--input-json', inputJson, '--output-json', outputJson, '--output-md', outputMd],
        {
          cwd: repoRoot,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);

      const report = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(report.summary.remoteMergedCandidates).toBe(1);
      expect(report.summary.remoteStaleCandidates).toBe(1);
      expect(report.sourceInventory.path).toBe(inputJson);

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toContain('Remote merged candidates (delete after operator approval)');
      expect(markdown).toContain('Remote stale candidates (operator triage required)');
      expect(markdown).toContain('pnpm run maintenance:branch:triage:render');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
