import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const validateScript = join(process.cwd(), 'scripts/ci/validate-assurance-summary.mjs');
const schemaPath = join(process.cwd(), 'schema/assurance-summary.schema.json');

describe('validate-assurance-summary CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'assurance-summary-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('accepts valid assurance summary', async () => {
    const summaryPath = join(workdir, 'assurance-summary.json');
    const summary = {
      schemaVersion: 'assurance-summary/v1',
      generatedAt: '2026-03-08T09:00:00.000Z',
      metadata: {
        generatedAtUtc: '2026-03-08T09:00:00.000Z',
        generatedAtLocal: '2026-03-08T18:00:00.000+09:00',
        timezoneOffset: '+09:00',
        gitCommit: '0123456789abcdef0123456789abcdef01234567',
        branch: 'main',
        runner: {
          name: 'local',
          os: 'linux',
          arch: 'x64',
          ci: false,
        },
        toolVersions: {
          node: 'v22.0.0',
        },
      },
      inputs: {
        assuranceProfile: 'fixtures/assurance/sample.assurance-profile.json',
        contextPacks: ['fixtures/context-pack/sample.context-pack.json'],
        verifyLiteSummary: null,
        formalSummaries: [],
        conformanceReport: null,
        counterexamples: [],
        evidenceManifests: [],
      },
      summary: {
        claimCount: 1,
        satisfiedClaims: 1,
        warningClaims: 0,
        claimsMissingRequiredLanes: 0,
        claimsMissingRequiredEvidenceKinds: 0,
        unlinkedCounterexamples: 0,
        warningCount: 0,
      },
      laneCoverage: {
        spec: { requiredClaims: 1, observedClaims: 1 },
        behavior: { requiredClaims: 0, observedClaims: 0 },
        adversarial: { requiredClaims: 0, observedClaims: 0 },
        model: { requiredClaims: 0, observedClaims: 0 },
        proof: { requiredClaims: 0, observedClaims: 0 },
        runtime: { requiredClaims: 0, observedClaims: 0 },
      },
      claims: [
        {
          claimId: 'no-negative-stock',
          statement: 'Inventory never becomes negative.',
          criticality: 'high',
          targetLevel: 'A3',
          minIndependentSources: 2,
          observedIndependentSources: 2,
          requiredLanes: ['spec'],
          observedLanes: ['spec'],
          missingLanes: [],
          requiredEvidenceKinds: ['schema'],
          observedEvidenceKinds: ['schema'],
          missingEvidenceKinds: [],
          counterexamples: {
            open: 0,
            resolved: 0,
            acceptedRisk: 0,
            total: 0,
          },
          independenceWarnings: [],
          status: 'satisfied',
          evidence: [
            {
              lane: 'spec',
              kind: 'schema',
              sourceKind: 'spec-derived',
              origin: 'context-pack',
              status: 'observed',
              artifactPath: 'fixtures/context-pack/sample.context-pack.json',
              detail: 'linked by context-pack assurance',
              claimRefs: ['no-negative-stock'],
              generatorLineage: 'context-pack-v1',
            },
          ],
        },
      ],
      warnings: [],
    };
    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(0);
    expect(result.stderr.toString()).toBe('');
  });

  it('fails when laneCoverage is incomplete', async () => {
    const summaryPath = join(workdir, 'assurance-summary.json');
    const summary = {
      schemaVersion: 'assurance-summary/v1',
      generatedAt: '2026-03-08T09:00:00.000Z',
      metadata: {
        generatedAtUtc: '2026-03-08T09:00:00.000Z',
        generatedAtLocal: '2026-03-08T18:00:00.000+09:00',
        timezoneOffset: '+09:00',
        gitCommit: '0123456789abcdef0123456789abcdef01234567',
        branch: 'main',
        runner: {
          name: 'local',
          os: 'linux',
          arch: 'x64',
          ci: false,
        },
        toolVersions: {
          node: 'v22.0.0',
        },
      },
      inputs: {
        assuranceProfile: 'fixtures/assurance/sample.assurance-profile.json',
        contextPacks: [],
        verifyLiteSummary: null,
        formalSummaries: [],
        conformanceReport: null,
        counterexamples: [],
        evidenceManifests: [],
      },
      summary: {
        claimCount: 0,
        satisfiedClaims: 0,
        warningClaims: 0,
        claimsMissingRequiredLanes: 0,
        claimsMissingRequiredEvidenceKinds: 0,
        unlinkedCounterexamples: 0,
        warningCount: 0,
      },
      laneCoverage: {
        spec: { requiredClaims: 0, observedClaims: 0 },
      },
      claims: [],
      warnings: [],
    };
    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('schema validation failed');
  });
});
