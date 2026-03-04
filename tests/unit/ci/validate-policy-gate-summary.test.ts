import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const validateScript = join(process.cwd(), 'scripts/ci/validate-policy-gate-summary.mjs');
const schemaPath = join(process.cwd(), 'schema/policy-gate-summary-v1.schema.json');

describe('validate-policy-gate-summary CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'policy-gate-summary-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('accepts valid policy-gate summary', async () => {
    const summaryPath = join(workdir, 'policy-gate-summary.json');
    const summary = {
      schemaVersion: 'policy-gate-summary/v1',
      contractId: 'policy-gate-summary.v1',
      generatedAtUtc: '2026-03-04T00:00:00.000Z',
      repository: 'itdojp/ae-framework',
      prNumber: 2406,
      changedFiles: ['package.json'],
      evaluation: {
        ok: true,
        errors: [],
        warnings: [],
        inferredRisk: { level: 'risk:low' },
        selectedRiskLabel: 'risk:low',
        currentRiskLabels: ['risk:low'],
        reviewTopology: 'team',
        approvals: 0,
        minApprovals: 1,
        policyMinApprovals: 1,
        topologyMinApprovals: 1,
        effectiveMinApprovals: 1,
        minApprovalsSource: 'policy',
        requiredLabels: [],
        missingRequiredLabels: [],
        requiredCheckResults: [],
        gateCheckResults: [],
      },
    };
    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], {
      cwd: workdir,
    });

    expect(result.status).toBe(0);
    expect(result.stderr.toString()).toBe('');
  });

  it('fails for invalid schemaVersion', async () => {
    const summaryPath = join(workdir, 'policy-gate-summary.json');
    const summary = {
      schemaVersion: '1.0.0',
      contractId: 'policy-gate-summary.v1',
      generatedAtUtc: '2026-03-04T00:00:00.000Z',
      repository: 'itdojp/ae-framework',
      prNumber: 2406,
      changedFiles: [],
      evaluation: {
        ok: true,
        errors: [],
        warnings: [],
        inferredRisk: { level: 'risk:low' },
        selectedRiskLabel: 'risk:low',
        currentRiskLabels: ['risk:low'],
        reviewTopology: 'team',
        approvals: 0,
        minApprovals: 1,
        policyMinApprovals: 1,
        topologyMinApprovals: 1,
        effectiveMinApprovals: 1,
        minApprovalsSource: 'policy',
        requiredLabels: [],
        missingRequiredLabels: [],
        requiredCheckResults: [],
        gateCheckResults: [],
      },
    };
    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], {
      cwd: workdir,
    });

    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('schema validation failed');
  });
});
