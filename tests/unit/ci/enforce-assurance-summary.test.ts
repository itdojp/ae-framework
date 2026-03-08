import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const enforceScript = join(process.cwd(), 'scripts/ci/enforce-assurance-summary.mjs');

describe('enforce-assurance-summary CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'assurance-enforce-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('passes for a satisfied assurance summary', async () => {
    const summaryPath = join(workdir, 'assurance-summary.json');
    await writeFile(
      summaryPath,
      JSON.stringify({
        summary: {
          claimCount: 1,
          warningClaims: 0,
          claimsMissingRequiredLanes: 0,
          claimsMissingRequiredEvidenceKinds: 0,
          unlinkedCounterexamples: 0,
          warningCount: 0,
        },
        claims: [
          {
            claimId: 'no-negative-stock',
            status: 'satisfied',
            missingLanes: [],
            missingEvidenceKinds: [],
            independenceWarnings: [],
            counterexamples: {
              open: 0,
            },
          },
        ],
      }),
    );

    const result = spawnSync(process.execPath, [enforceScript, summaryPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(0);
    expect(result.stdout.toString()).toContain('result: pass');
  });

  it('fails when warnings remain in the assurance summary', async () => {
    const summaryPath = join(workdir, 'assurance-summary.json');
    await writeFile(
      summaryPath,
      JSON.stringify({
        summary: {
          claimCount: 1,
          warningClaims: 1,
          claimsMissingRequiredLanes: 1,
          claimsMissingRequiredEvidenceKinds: 0,
          unlinkedCounterexamples: 0,
          warningCount: 2,
        },
        claims: [
          {
            claimId: 'no-negative-stock',
            status: 'warning',
            missingLanes: ['spec'],
            missingEvidenceKinds: [],
            independenceWarnings: ['missing-spec-derived-evidence'],
            counterexamples: {
              open: 0,
            },
          },
        ],
      }),
    );

    const result = spawnSync(process.execPath, [enforceScript, summaryPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('result: fail');
    expect(result.stderr.toString()).toContain('warningClaims=1');
    expect(result.stderr.toString()).toContain('claim no-negative-stock status=warning');
    expect(result.stderr.toString()).toContain('claim no-negative-stock independenceWarnings=missing-spec-derived-evidence');
  });

  it('fails when the summary file does not exist', () => {
    const result = spawnSync(process.execPath, [enforceScript, 'missing.json'], {
      cwd: workdir,
    });
    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('summary not found');
  });
});
