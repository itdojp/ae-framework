import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/maintenance/remote-cleanup-refresh-audit.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

describe.sequential('remote-cleanup-refresh-audit script', () => {
  it('confirms verified-absent branches stay out of refreshed triage', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs([])).toMatchObject({
      postVerifySummaryJson: 'tmp/maintenance/remote-cleanup-post-apply-verify/summary.json',
      refreshedTriageJson: 'tmp/maintenance/remote-branch-triage.json',
      outputDir: 'tmp/maintenance/remote-cleanup-refresh-audit',
    });

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-refresh-audit-'));
    const postVerifySummaryPath = join(sandbox, 'post-verify-summary.json');
    const refreshedTriagePath = join(sandbox, 'remote-branch-triage.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeFileSync(
        postVerifySummaryPath,
        `${JSON.stringify(
          {
            deleted: [{ branch: 'docs/stale-a', status: 'verified-absent', actualOid: '' }],
          },
          null,
          2,
        )}\n`,
      );
      writeFileSync(
        refreshedTriagePath,
        `${JSON.stringify(
          {
            remoteMerged: [{ branch: 'docs/merged-a' }],
            remoteStale: [{ branch: 'docs/stale-b' }],
          },
          null,
          2,
        )}\n`,
      );

      const result = spawnSync(
        'node',
        [scriptPath, '--post-verify-summary-json', postVerifySummaryPath, '--refreshed-triage-json', refreshedTriagePath, '--output-dir', outputDir],
        {
          cwd: repoRoot,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('verifiedAbsent=1 confirmed=1 reappeared=0 recreated=0');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.counts.confirmedRemoved).toBe(1);
      expect(summary.counts.reappearedInTriage).toBe(0);
      expect(summary.counts.recreatedRefInput).toBe(0);
      expect(summary.audit).toEqual([
        expect.objectContaining({ branch: 'docs/stale-a', status: 'confirmed-removed' }),
      ]);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('reports branches that reappear in refreshed triage', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-refresh-audit-reappear-'));
    const postVerifySummaryPath = join(sandbox, 'post-verify-summary.json');
    const refreshedTriagePath = join(sandbox, 'remote-branch-triage.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeFileSync(
        postVerifySummaryPath,
        `${JSON.stringify(
          {
            deleted: [{ branch: 'docs/stale-a', status: 'verified-absent', actualOid: '' }],
          },
          null,
          2,
        )}\n`,
      );
      writeFileSync(
        refreshedTriagePath,
        `${JSON.stringify(
          {
            remoteMerged: [],
            remoteStale: [{ branch: 'docs/stale-a' }],
          },
          null,
          2,
        )}\n`,
      );

      const result = spawnSync(
        'node',
        [scriptPath, '--post-verify-summary-json', postVerifySummaryPath, '--refreshed-triage-json', refreshedTriagePath, '--output-dir', outputDir],
        {
          cwd: repoRoot,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.counts.reappearedInTriage).toBe(1);
      expect(summary.audit).toEqual([
        expect.objectContaining({
          branch: 'docs/stale-a',
          status: 'reappeared-in-triage',
          refreshedLocations: ['remoteStale'],
        }),
      ]);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('tracks recreated refs separately from verified-absent refresh input', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-refresh-audit-recreated-'));
    const postVerifySummaryPath = join(sandbox, 'post-verify-summary.json');
    const refreshedTriagePath = join(sandbox, 'remote-branch-triage.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeFileSync(
        postVerifySummaryPath,
        `${JSON.stringify(
          {
            deleted: [
              { branch: 'docs/stale-a', status: 'verified-absent', expectedOid: 'oid-a', actualOid: '' },
              { branch: 'docs/stale-b', status: 'recreated-ref', expectedOid: 'oid-old', actualOid: 'oid-new' },
            ],
          },
          null,
          2,
        )}\n`,
      );
      writeFileSync(
        refreshedTriagePath,
        `${JSON.stringify(
          {
            remoteMerged: [],
            remoteStale: [{ branch: 'docs/stale-b' }],
          },
          null,
          2,
        )}\n`,
      );

      const result = spawnSync(
        'node',
        [scriptPath, '--post-verify-summary-json', postVerifySummaryPath, '--refreshed-triage-json', refreshedTriagePath, '--output-dir', outputDir],
        {
          cwd: repoRoot,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('verifiedAbsent=1 confirmed=1 reappeared=0 recreated=1');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.counts.verifiedAbsentInput).toBe(1);
      expect(summary.counts.confirmedRemoved).toBe(1);
      expect(summary.counts.reappearedInTriage).toBe(0);
      expect(summary.counts.recreatedRefInput).toBe(1);
      expect(summary.counts.recreatedRefInTriage).toBe(1);
      expect(summary.counts.recreatedRefOutsideTriage).toBe(0);
      expect(summary.audit).toEqual([
        expect.objectContaining({ branch: 'docs/stale-a', status: 'confirmed-removed' }),
      ]);
      expect(summary.recreated).toEqual([
        expect.objectContaining({
          branch: 'docs/stale-b',
          status: 'recreated-ref-in-triage',
          expectedOid: 'oid-old',
          actualOid: 'oid-new',
          refreshedLocations: ['remoteStale'],
        }),
      ]);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects invalid post-verify summary payloads', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-refresh-audit-invalid-'));
    const postVerifySummaryPath = join(sandbox, 'post-verify-summary.json');
    const refreshedTriagePath = join(sandbox, 'remote-branch-triage.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeFileSync(postVerifySummaryPath, '{}\n');
      writeFileSync(refreshedTriagePath, '{"remoteMerged":[],"remoteStale":[]}\n');

      const result = spawnSync(
        'node',
        [scriptPath, '--post-verify-summary-json', postVerifySummaryPath, '--refreshed-triage-json', refreshedTriagePath, '--output-dir', outputDir],
        {
          cwd: repoRoot,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('post-verify summary is missing deleted rows');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects malformed refreshed triage payloads', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-refresh-audit-malformed-'));
    const postVerifySummaryPath = join(sandbox, 'post-verify-summary.json');
    const refreshedTriagePath = join(sandbox, 'remote-branch-triage.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeFileSync(
        postVerifySummaryPath,
        `${JSON.stringify(
          {
            deleted: [{ branch: 'docs/stale-a', status: 'verified-absent', actualOid: '' }],
          },
          null,
          2,
        )}\n`,
      );
      writeFileSync(refreshedTriagePath, '{"remoteStale":[]}\n');

      const result = spawnSync(
        'node',
        [scriptPath, '--post-verify-summary-json', postVerifySummaryPath, '--refreshed-triage-json', refreshedTriagePath, '--output-dir', outputDir],
        {
          cwd: repoRoot,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('refreshed triage is missing remoteMerged[]');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
