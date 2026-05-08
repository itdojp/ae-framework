import { afterEach, describe, expect, it } from 'vitest';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const generateScript = resolve(repoRoot, 'scripts/change-package/generate.mjs');
const policyPath = resolve(repoRoot, 'policy/risk-policy.yml');
const workdirs: string[] = [];
const isolatedGenerateEnv = {
  ...process.env,
  GITHUB_EVENT_PATH: '',
  GITHUB_HEAD_REF: '',
  GITHUB_BASE_REF: '',
  GITHUB_REPOSITORY: '',
  PR_NUMBER: '',
  CHANGE_PACKAGE_LABELS: '',
  CHANGE_PACKAGE_CHANGED_FILES: '',
  CHANGE_PACKAGE_INTENT_SUMMARY: '',
};

async function createWorkdir(prefix: string): Promise<string> {
  const workdir = await mkdtemp(join(tmpdir(), prefix));
  workdirs.push(workdir);
  return workdir;
}

afterEach(async () => {
  await Promise.all(workdirs.splice(0).map((workdir) => rm(workdir, { recursive: true, force: true })));
});

async function writeJson(filePath: string, payload: unknown): Promise<void> {
  await mkdir(dirname(filePath), { recursive: true });
  await writeFile(filePath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
}

async function writeV2InputArtifacts(workdir: string): Promise<{
  manifestPath: string;
  policyDecisionPath: string;
  assuranceSummaryPath: string;
}> {
  const manifestPath = join(workdir, 'artifacts', 'assurance', 'claim-evidence-manifest.json');
  const policyDecisionPath = join(workdir, 'artifacts', 'ci', 'policy-decision-js-v1.json');
  const assuranceSummaryPath = join(workdir, 'artifacts', 'assurance', 'assurance-summary.json');

  await writeJson(join(workdir, 'artifacts', 'testing', 'property-summary.json'), { status: 'pass' });
  await writeJson(join(workdir, 'artifacts', 'formal', 'no-negative-summary.json'), { status: 'pass' });
  await writeJson(join(workdir, 'artifacts', 'runtime', 'manual-review.json'), { status: 'active' });

  await writeJson(manifestPath, {
    schemaVersion: 'claim-evidence-manifest/v1',
    generatedAt: '2026-05-06T00:00:00.000Z',
    sourceArtifacts: [
      {
        id: 'manual',
        kind: 'manual',
        path: 'artifacts/assurance/claim-evidence-manifest.json',
        present: true,
        required: true,
        schemaVersion: 'claim-evidence-manifest/v1',
      },
    ],
    claims: [
      {
        id: 'manual-review',
        statement: 'Manual review remains active for high-risk reservations.',
        criticality: 'medium',
        targetLevel: 'A2',
        achievedLevel: 'A2',
        status: 'waived',
        evidenceRefs: [
          {
            id: 'manual-review-runtime',
            kind: 'runtime',
            artifactPath: 'artifacts/runtime/manual-review.json',
            sourceArtifactId: 'manual',
          },
        ],
        proofObligationRefs: [],
        missingEvidenceRefs: [],
        waiverRefs: [
          {
            id: 'waiver-manual-review',
            sourceArtifactId: 'manual',
            status: 'active',
            owner: '@team-risk',
            expires: '2099-12-31',
            reason: 'Manual control is active while model validation evidence is collected.',
          },
        ],
        notes: [],
      },
      {
        id: 'no-negative-stock',
        statement: 'Inventory stock never becomes negative.',
        criticality: 'high',
        targetLevel: 'A3',
        achievedLevel: 'A3',
        status: 'satisfied',
        evidenceRefs: [
          {
            id: 'property-summary',
            kind: 'behavior',
            artifactPath: 'artifacts/testing/property-summary.json',
            sourceArtifactId: 'manual',
          },
        ],
        proofObligationRefs: [
          {
            id: 'obl-no-negative-stock',
            status: 'discharged',
            sourceArtifactId: 'manual',
            artifactPath: 'artifacts/formal/no-negative-summary.json',
            method: 'tla',
          },
        ],
        missingEvidenceRefs: [],
        waiverRefs: [],
        notes: [],
      },
    ],
    summary: {
      totalClaims: 2,
      fullySupported: 1,
      partiallySupported: 0,
      waived: 1,
      unresolved: 0,
    },
  });

  await writeJson(policyDecisionPath, {
    schemaVersion: '1.0.0',
    contractId: 'policy-decision.v1',
    evaluation: {
      assurance: {
        result: 'waived',
        claims: [
          { claimId: 'manual-review', result: 'waived', status: 'waived' },
          { claimId: 'no-negative-stock', result: 'pass', status: 'satisfied' },
        ],
        waivers: [
          {
            owner: '@team-risk',
            expires: '2099-12-31',
            reason: 'Manual control is active while model validation evidence is collected.',
            claimId: 'manual-review',
          },
        ],
      },
    },
  });

  await writeJson(assuranceSummaryPath, {
    schemaVersion: 'assurance-summary/v1',
    summary: {
      claimCount: 2,
      satisfiedClaims: 1,
      warningClaims: 1,
      warningCount: 1,
    },
    claims: [],
  });

  return { manifestPath, policyDecisionPath, assuranceSummaryPath };
}

async function writeClaimLevelSummaryArtifact(workdir: string): Promise<string> {
  const claimLevelSummaryPath = join(workdir, 'artifacts', 'assurance', 'claim-level-summary.json');
  await writeJson(claimLevelSummaryPath, {
    schemaVersion: 'claim-level-summary/v1',
    generatedAt: '2026-05-08T00:00:00.000Z',
    source: {
      repository: 'itdojp/ae-framework',
      prNumber: 3309,
      baseRef: 'main',
      headRef: 'feat/3309-change-package-proof',
    },
    inputs: {
      claimEvidenceManifest: {
        id: 'claim-evidence-manifest',
        path: 'artifacts/assurance/claim-evidence-manifest.json',
        present: true,
        required: true,
      },
      policyGateSummary: {
        id: 'policy-gate-summary',
        path: 'artifacts/ci/policy-gate-summary.json',
        present: true,
        required: false,
      },
      temporaryOverrides: [],
      changePackageV2: null,
    },
    summary: {
      totalClaims: 3,
      satisfied: 0,
      tested: 1,
      modelChecked: 0,
      proved: 0,
      runtimeMitigated: 1,
      waived: 0,
      unresolved: 0,
      failed: 1,
      notApplicable: 0,
      enforcedDecisions: 1,
      reportOnlyDecisions: 2,
    },
    claims: [
      {
        claimId: 'reservation-tested',
        statement: 'Reservation behavior is covered by tests.',
        criticality: 'medium',
        targetLevel: 'A2',
        achievedLevel: 'A2',
        state: 'tested',
        stateRationale: 'Behavior evidence is observed.',
        decision: {
          mode: 'report-only',
          result: 'pass',
          enforced: false,
          reason: 'Test evidence is present.',
          sourceArtifactId: 'policy-gate-summary',
          evidenceRefs: ['ev-reservation-test'],
          missingEvidenceRefs: [],
          waiverRefs: [],
        },
        evidenceRefs: [
          {
            id: 'ev-reservation-test',
            kind: 'behavior',
            status: 'observed',
            artifactPath: 'artifacts/testing/property-summary.json',
            sourceArtifactId: 'verify-lite',
            description: 'Behavior test evidence.',
          },
        ],
        missingEvidenceRefs: [],
        waiverRefs: [],
        assumptions: [],
        runtimeControls: [],
        notes: ['requirement:docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md'],
      },
      {
        claimId: 'rollout-runtime',
        statement: 'Rollout risk is mitigated by runtime controls.',
        criticality: 'high',
        targetLevel: 'A3',
        achievedLevel: 'A2',
        state: 'runtime-mitigated',
        stateRationale: 'Runtime control is linked.',
        decision: {
          mode: 'report-only',
          result: 'report-only',
          enforced: false,
          reason: 'Runtime mitigation remains distinct from proof.',
          sourceArtifactId: 'policy-gate-summary',
          evidenceRefs: ['ev-runtime-control'],
          missingEvidenceRefs: [],
          waiverRefs: [],
        },
        evidenceRefs: [
          {
            id: 'ev-runtime-control',
            kind: 'runtime',
            status: 'observed',
            artifactPath: 'artifacts/runtime/manual-review.json',
            sourceArtifactId: 'change-package-v2',
            description: 'Runtime rollout guard.',
          },
        ],
        missingEvidenceRefs: [],
        waiverRefs: [],
        assumptions: [
          {
            id: 'assumption-rollout-window',
            statement: 'Rollback window remains staffed.',
            status: 'residual-risk',
            artifactPath: 'docs/ci/change-package.md',
          },
        ],
        runtimeControls: [
          {
            id: 'rollout_guard_violation',
            kind: 'alert',
            description: 'Rollback if rollout guard emits an alert.',
          },
        ],
        notes: [],
      },
      {
        claimId: 'strict-proof-failure',
        statement: 'Strict proof still has an open counterexample.',
        criticality: 'critical',
        targetLevel: 'A4',
        achievedLevel: 'A1',
        state: 'failed',
        stateRationale: 'Proof evidence failed.',
        decision: {
          mode: 'strict',
          result: 'block',
          enforced: true,
          reason: 'Failed proof blocks strict enforcement.',
          sourceArtifactId: 'policy-gate-summary',
          evidenceRefs: ['ev-proof-failed'],
          missingEvidenceRefs: [],
          waiverRefs: [],
        },
        evidenceRefs: [
          {
            id: 'ev-proof-failed',
            kind: 'proof',
            status: 'failed',
            artifactPath: 'artifacts/formal/no-negative-summary.json',
            sourceArtifactId: 'formal-summary',
            description: 'Failed proof evidence.',
          },
        ],
        missingEvidenceRefs: [],
        waiverRefs: [],
        assumptions: [],
        runtimeControls: [],
        notes: [],
      },
    ],
  });
  return claimLevelSummaryPath;
}

describe('change-package generate', () => {
  it('generates change-package json/md from changed files and event payload', async () => {
    const workdir = await createWorkdir('change-package-generate-');
    const changedFilesPath = join(workdir, 'changed-files.txt');
    const eventPath = join(workdir, 'event.json');
    const outputJsonPath = join(workdir, 'artifacts', 'change-package', 'change-package.json');
    const outputMarkdownPath = join(workdir, 'artifacts', 'change-package', 'change-package.md');

    await writeFile(
      changedFilesPath,
      [
        '.github/workflows/pr-ci-status-comment.yml',
        'schema/change-package.schema.json',
      ].join('\n'),
      'utf8',
    );

    await writeFile(
      eventPath,
      `${JSON.stringify({
        repository: { full_name: 'itdojp/ae-framework' },
        pull_request: {
          number: 2289,
          title: 'Introduce Change Package v1',
          base: { ref: 'main' },
          head: { ref: 'feat/2289-change-package-v1' },
          labels: [{ name: 'risk:high' }],
        },
      }, null, 2)}\n`,
      'utf8',
    );

    await mkdir(join(workdir, 'artifacts', 'verify-lite'), { recursive: true });
    await writeFile(
      join(workdir, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json'),
      `${JSON.stringify({ status: 'ok' })}\n`,
      'utf8',
    );

    const result = spawnSync(process.execPath, [
      generateScript,
      '--policy', policyPath,
      '--changed-files-file', changedFilesPath,
      '--event-path', eventPath,
      '--artifact-root', workdir,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--mode', 'detailed',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      env: isolatedGenerateEnv,
    });

    expect(result.status).toBe(0);

    const generated = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      schemaVersion: string;
      source: { repository: string; prNumber: number; baseRef: string; headRef: string };
      scope: { changedFileCount: number; areas: string[] };
      risk: {
        selected: string;
        requiredLabels: string[];
        missingRequiredLabels: string[];
        rationale: {
          highRiskPathMatches: string[];
        };
      };
      reproducibility: {
        commands: string[];
      };
      evidence: { presentCount: number; missingCount: number };
      exceptions: Array<{ code: string; message: string }>;
    };

    expect(generated.schemaVersion).toBe('change-package/v1');
    expect(generated.source.repository).toBe('itdojp/ae-framework');
    expect(generated.source.prNumber).toBe(2289);
    expect(generated.source.baseRef).toBe('main');
    expect(generated.source.headRef).toBe('feat/2289-change-package-v1');
    expect(generated.scope.changedFileCount).toBe(2);
    expect(generated.scope.areas).toContain('ci');
    expect(generated.scope.areas).toContain('schema');
    expect(generated.risk.selected).toBe('risk:high');
    expect(generated.risk.requiredLabels).toContain('run-ci-extended');
    expect(generated.risk.requiredLabels).toContain('enforce-artifacts');
    expect(generated.risk.missingRequiredLabels).toContain('run-ci-extended');
    expect(generated.risk.rationale.highRiskPathMatches).toContain('.github/workflows/pr-ci-status-comment.yml');
    expect(
      generated.reproducibility.commands.some(
        (command) => command.includes('scripts/trace/run-kvonce-conformance.sh')
          && command.includes('pnpm run artifacts:validate -- --strict=true'),
      ),
    ).toBe(true);
    expect(generated.evidence.presentCount).toBe(1);
    expect(generated.evidence.missingCount).toBeGreaterThan(0);
    expect(generated.exceptions.some((item) => item.code === 'missing-required-labels')).toBe(true);

    const markdown = await readFile(outputMarkdownPath, 'utf8');
    expect(markdown).toContain('## Change Package');
    expect(markdown).toContain('### Evidence');
  });

  it('records conflicting risk labels as exceptions and keeps high-risk true when inferred high', async () => {
    const workdir = await createWorkdir('change-package-generate-risk-conflict-');
    const changedFilesPath = join(workdir, 'changed-files.txt');
    const eventPath = join(workdir, 'event.json');
    const outputJsonPath = join(workdir, 'artifacts', 'change-package', 'change-package.json');
    const outputMarkdownPath = join(workdir, 'artifacts', 'change-package', 'change-package.md');

    await writeFile(
      changedFilesPath,
      ['schema/change-package.schema.json'].join('\n'),
      'utf8',
    );

    await writeFile(
      eventPath,
      `${JSON.stringify({
        repository: { full_name: 'itdojp/ae-framework' },
        pull_request: {
          number: 2290,
          title: 'Risk label conflict sample',
          base: { ref: 'main' },
          head: { ref: 'feat/risk-conflict' },
          labels: [{ name: 'risk:low' }, { name: 'risk:high' }],
        },
      }, null, 2)}\n`,
      'utf8',
    );

    const result = spawnSync(process.execPath, [
      generateScript,
      '--policy', policyPath,
      '--changed-files-file', changedFilesPath,
      '--event-path', eventPath,
      '--artifact-root', workdir,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--mode', 'digest',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      env: isolatedGenerateEnv,
    });

    expect(result.status).toBe(0);

    const generated = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      risk: {
        selected: string;
        inferred: string;
        isHighRisk: boolean;
      };
      exceptions: Array<{ code: string; message: string }>;
    };

    expect(generated.risk.selected).toBe('risk:high');
    expect(generated.risk.inferred).toBe('risk:high');
    expect(generated.risk.isHighRisk).toBe(true);
    expect(generated.exceptions.some((item) => item.code === 'multiple-risk-labels')).toBe(true);

    const markdown = await readFile(outputMarkdownPath, 'utf8');
    expect(markdown).toContain('### Change Package');
  });

  it('generates change-package v2 from claim evidence, policy decision, and assurance inputs', async () => {
    const workdir = await createWorkdir('change-package-generate-v2-');
    const changedFilesPath = join(workdir, 'changed-files.txt');
    const eventPath = join(workdir, 'event.json');
    const outputJsonPath = join(workdir, 'artifacts', 'change-package', 'change-package-v2.json');
    const outputMarkdownPath = join(workdir, 'artifacts', 'change-package', 'change-package-v2.md');
    const { manifestPath, policyDecisionPath, assuranceSummaryPath } = await writeV2InputArtifacts(workdir);

    await writeFile(changedFilesPath, ['scripts/change-package/generate.mjs'].join('\n'), 'utf8');
    await writeJson(eventPath, {
      repository: { full_name: 'itdojp/ae-framework' },
      pull_request: {
        number: 3246,
        title: 'Integrate change-package v2',
        base: { ref: 'main' },
        head: { ref: 'feat/3246-change-package-v2' },
        labels: [{ name: 'risk:low' }],
      },
    });

    const result = spawnSync(process.execPath, [
      generateScript,
      '--policy', policyPath,
      '--schema-version', 'v2',
      '--changed-files-file', changedFilesPath,
      '--event-path', eventPath,
      '--artifact-root', workdir,
      '--claim-evidence-manifest', manifestPath,
      '--policy-decision', policyDecisionPath,
      '--assurance-summary', assuranceSummaryPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--mode', 'detailed',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      env: isolatedGenerateEnv,
    });

    expect(result.status, result.stderr || result.stdout).toBe(0);

    const generated = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      schemaVersion: string;
      assurance: { targetLevel: string; achievedLevel: string; status: string };
      claims: Array<{ id: string; status: string; artifactRefs: string[] }>;
      proofObligations: Array<{ id: string; claimId: string; status: string }>;
      waivers: Array<{ owner: string; relatedClaimIds: string[] }>;
      evidence: { items: Array<{ id: string; present: boolean }> };
    };

    expect(generated.schemaVersion).toBe('change-package/v2');
    expect(generated.assurance).toEqual({ targetLevel: 'A3', achievedLevel: 'A2', status: 'waived' });
    expect(generated.claims).toHaveLength(2);
    expect(generated.claims.find((claim) => claim.id === 'manual-review')?.status).toBe('waived');
    expect(generated.claims.find((claim) => claim.id === 'no-negative-stock')?.artifactRefs).toContain('artifacts/formal/no-negative-summary.json');
    expect(generated.proofObligations).toContainEqual(expect.objectContaining({
      id: 'obl-no-negative-stock',
      claimId: 'no-negative-stock',
      status: 'discharged',
    }));
    expect(generated.waivers).toContainEqual(expect.objectContaining({
      owner: '@team-risk',
      relatedClaimIds: ['manual-review'],
    }));
    expect(generated.evidence.items).toContainEqual(expect.objectContaining({ id: 'claimEvidenceManifest', present: true }));
    expect(generated.evidence.items).toContainEqual(expect.objectContaining({ id: 'policyDecision', present: true }));

    const markdown = await readFile(outputMarkdownPath, 'utf8');
    expect(markdown).toContain('### Claims');
    expect(markdown).toContain('### Proof Obligations');
    expect(markdown).toContain('### Waivers');
  });

  it('projects claim-level-summary states, release controls, policy decision, and residual risks into v2', async () => {
    const workdir = await createWorkdir('change-package-generate-claim-level-v2-');
    const changedFilesPath = join(workdir, 'changed-files.txt');
    const outputJsonPath = join(workdir, 'artifacts', 'change-package', 'change-package-v2.json');
    const outputMarkdownPath = join(workdir, 'artifacts', 'change-package', 'change-package-v2.md');
    const { manifestPath, policyDecisionPath, assuranceSummaryPath } = await writeV2InputArtifacts(workdir);
    const claimLevelSummaryPath = await writeClaimLevelSummaryArtifact(workdir);

    await writeFile(
      changedFilesPath,
      [
        'docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md',
        'scripts/change-package/generate.mjs',
      ].join('\n'),
      'utf8',
    );

    const result = spawnSync(process.execPath, [
      generateScript,
      '--policy', policyPath,
      '--schema-version', 'v2',
      '--changed-files-file', changedFilesPath,
      '--artifact-root', workdir,
      '--claim-evidence-manifest', manifestPath,
      '--policy-decision', policyDecisionPath,
      '--assurance-summary', assuranceSummaryPath,
      '--claim-level-summary', claimLevelSummaryPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--mode', 'detailed',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      env: isolatedGenerateEnv,
    });

    expect(result.status, result.stderr || result.stdout).toBe(0);

    const generated = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      assurance: { status: string };
      requirements: { changedRefs: string[] };
      validationLanes: Array<{ id: string; status: string }>;
      policyDecision: { result: string; mode: string; enforced: boolean };
      releaseControls: { preDeployChecks: string[]; postDeployChecks: string[]; rollbackSignals: string[] };
      residualRisks: Array<{ id: string; claimIds: string[] }>;
      claims: Array<{ id: string; status: string; targetLevel: string; achievedLevel: string }>;
      evidence: { items: Array<{ id: string; present: boolean }> };
    };

    expect(generated.assurance.status).toBe('failed');
    expect(generated.requirements.changedRefs).toContain('docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md');
    expect(generated.claims).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: 'rollout-runtime', status: 'runtime-mitigated', targetLevel: 'A3', achievedLevel: 'A2' }),
      expect.objectContaining({ id: 'strict-proof-failure', status: 'failed', targetLevel: 'A4', achievedLevel: 'A1' }),
    ]));
    expect(generated.validationLanes).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: 'proof', status: 'fail' }),
      expect.objectContaining({ id: 'runtime', status: 'pass' }),
    ]));
    expect(generated.policyDecision).toMatchObject({ result: 'waived', mode: 'unknown', enforced: false });
    expect(generated.releaseControls.preDeployChecks).toContain('pnpm run verify:lite');
    expect(generated.releaseControls.postDeployChecks).toContain('post-deploy-verify workflow or release verification artifact required before production rollout');
    expect(generated.releaseControls.rollbackSignals).toContain('post-deploy-verify.status=fail');
    expect(generated.residualRisks).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: 'claim:strict-proof-failure:failed', claimIds: ['strict-proof-failure'] }),
      expect.objectContaining({ id: 'assumption:assumption-rollout-window', claimIds: ['rollout-runtime'] }),
    ]));
    expect(generated.evidence.items).toContainEqual(expect.objectContaining({ id: 'claimLevelSummary', present: true }));

    const markdown = await readFile(outputMarkdownPath, 'utf8');
    expect(markdown).toContain('evidence package:');
    expect(markdown).toContain('claim states: satisfied=');
    expect(markdown).toContain('### Release / Post-deploy Controls');
    expect(markdown).toContain('### Residual Risks');
  });

  it('derives v2 assurance status from unresolved and partial assurance-summary claims', async () => {
    for (const [sourceStatus, expectedAssuranceStatus] of [
      ['unresolved', 'unresolved'],
      ['partial', 'partial'],
      ['warning', 'partial'],
    ]) {
      const workdir = await createWorkdir(`change-package-generate-v2-${sourceStatus}-`);
      const changedFilesPath = join(workdir, 'changed-files.txt');
      const assuranceSummaryPath = join(workdir, 'artifacts', 'assurance', 'assurance-summary.json');
      const outputJsonPath = join(workdir, 'artifacts', 'change-package', 'change-package-v2.json');
      const outputMarkdownPath = join(workdir, 'artifacts', 'change-package', 'change-package-v2.md');

      await writeFile(changedFilesPath, ['docs/ci/change-package.md'].join('\n'), 'utf8');
      await writeJson(assuranceSummaryPath, {
        schemaVersion: 'assurance-summary/v1',
        summary: {
          claimCount: 1,
          satisfiedClaims: 0,
          warningClaims: 1,
          warningCount: 1,
        },
        claims: [
          {
            claimId: 'runtime-coverage',
            statement: 'Runtime coverage evidence is not yet complete.',
            status: sourceStatus,
            targetLevel: 'A2',
            criticality: 'high',
            evidence: [],
          },
        ],
      });

      const result = spawnSync(process.execPath, [
        generateScript,
        '--policy', policyPath,
        '--schema-version', 'v2',
        '--changed-files-file', changedFilesPath,
        '--artifact-root', workdir,
        '--claim-evidence-manifest', join(workdir, 'missing-claim-evidence-manifest.json'),
        '--policy-decision', join(workdir, 'missing-policy-decision.json'),
        '--assurance-summary', assuranceSummaryPath,
        '--output-json', outputJsonPath,
        '--output-md', outputMarkdownPath,
        '--mode', 'digest',
      ], {
        cwd: repoRoot,
        encoding: 'utf8',
        env: isolatedGenerateEnv,
      });

      expect(result.status, result.stderr || result.stdout).toBe(0);

      const generated = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
        assurance: { achievedLevel: string; status: string };
        claims: Array<{ id: string; status: string }>;
      };

      expect(generated.claims).toContainEqual(expect.objectContaining({
        id: 'runtime-coverage',
        status: 'unresolved',
      }));
      expect(generated.assurance.achievedLevel).toBe('A1');
      expect(generated.assurance.status).toBe(expectedAssuranceStatus);
    }
  });

  it('dual-writes v1 and v2 change packages without changing the v1 default output', async () => {
    const workdir = await createWorkdir('change-package-generate-dual-');
    const changedFilesPath = join(workdir, 'changed-files.txt');
    const outputJsonPath = join(workdir, 'artifacts', 'change-package', 'change-package.json');
    const outputMarkdownPath = join(workdir, 'artifacts', 'change-package', 'change-package.md');
    const v2OutputJsonPath = join(workdir, 'artifacts', 'change-package', 'change-package-v2.json');
    const v2OutputMarkdownPath = join(workdir, 'artifacts', 'change-package', 'change-package-v2.md');
    const { manifestPath, policyDecisionPath, assuranceSummaryPath } = await writeV2InputArtifacts(workdir);

    await writeFile(changedFilesPath, ['docs/ci/change-package.md'].join('\n'), 'utf8');

    const result = spawnSync(process.execPath, [
      generateScript,
      '--policy', policyPath,
      '--dual-write',
      '--changed-files-file', changedFilesPath,
      '--artifact-root', workdir,
      '--claim-evidence-manifest', manifestPath,
      '--policy-decision', policyDecisionPath,
      '--assurance-summary', assuranceSummaryPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--v2-output-json', v2OutputJsonPath,
      '--v2-output-md', v2OutputMarkdownPath,
      '--mode', 'digest',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      env: isolatedGenerateEnv,
    });

    expect(result.status, result.stderr || result.stdout).toBe(0);

    const v1 = JSON.parse(await readFile(outputJsonPath, 'utf8')) as { schemaVersion: string };
    const v2 = JSON.parse(await readFile(v2OutputJsonPath, 'utf8')) as { schemaVersion: string; claims: unknown[] };
    const v1Markdown = await readFile(outputMarkdownPath, 'utf8');
    const v2Markdown = await readFile(v2OutputMarkdownPath, 'utf8');

    expect(v1.schemaVersion).toBe('change-package/v1');
    expect(v2.schemaVersion).toBe('change-package/v2');
    expect(v2.claims).toHaveLength(2);
    expect(v1Markdown).toContain('### Change Package');
    expect(v2Markdown).toContain('claims=2');
  });
});
