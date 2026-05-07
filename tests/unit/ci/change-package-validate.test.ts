import { afterEach, describe, expect, it } from 'vitest';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const validateScript = resolve(repoRoot, 'scripts/change-package/validate.mjs');
const schemaPath = resolve(repoRoot, 'schema/change-package.schema.json');
const v2SchemaPath = resolve(repoRoot, 'schema/change-package-v2.schema.json');
const fixturePath = resolve(repoRoot, 'fixtures/change-package/sample.change-package.json');
const workdirs: string[] = [];

async function createWorkdir(prefix: string): Promise<string> {
  const workdir = await mkdtemp(join(tmpdir(), prefix));
  workdirs.push(workdir);
  return workdir;
}

afterEach(async () => {
  await Promise.all(workdirs.splice(0).map((workdir) => rm(workdir, { recursive: true, force: true })));
});

async function loadFixture(): Promise<Record<string, unknown>> {
  const raw = await readFile(fixturePath, 'utf8');
  return JSON.parse(raw) as Record<string, unknown>;
}

async function writeJson(filePath: string, payload: unknown): Promise<void> {
  await mkdir(dirname(filePath), { recursive: true });
  await writeFile(filePath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
}

async function writeV2Fixture(workdir: string): Promise<{ inputPath: string; policyDecisionPath: string }> {
  const inputPath = join(workdir, 'change-package-v2.json');
  const policyDecisionPath = join(workdir, 'policy-decision-js-v1.json');

  await writeJson(join(workdir, 'artifacts', 'testing', 'property-summary.json'), { status: 'pass' });
  await writeJson(join(workdir, 'artifacts', 'formal', 'no-negative-summary.json'), { status: 'pass' });
  await writeJson(join(workdir, 'artifacts', 'runtime', 'manual-review.json'), { status: 'active' });

  await writeJson(inputPath, {
    schemaVersion: 'change-package/v2',
    generatedAt: '2026-05-06T00:00:00.000Z',
    policyPath: 'policy/risk-policy.yml',
    source: {
      repository: 'itdojp/ae-framework',
      prNumber: 3246,
      baseRef: 'main',
      headRef: 'feat/3246-change-package-v2',
    },
    intent: { summary: 'Validate change-package v2.' },
    scope: {
      changedFiles: ['scripts/change-package/validate.mjs'],
      changedFileCount: 1,
      areas: ['scripts'],
    },
    risk: {
      selected: 'risk:low',
      inferred: 'risk:low',
      isHighRisk: false,
      requiredLabels: [],
      missingRequiredLabels: [],
      rationale: { highRiskPathMatches: [], forceHighRiskTriggers: [] },
    },
    evidence: {
      artifactRoot: '.',
      items: [
        {
          id: 'verifyLiteSummary',
          path: 'artifacts/testing/property-summary.json',
          description: 'test evidence',
          present: true,
        },
      ],
      presentCount: 1,
      missingCount: 0,
    },
    reproducibility: { commands: ['pnpm run verify:lite'] },
    rolloutPlan: {
      strategy: 'manual-approval-and-gate-green',
      references: ['policy/risk-policy.yml'],
      notes: ['Validate v2 contract.'],
    },
    monitoringPlan: {
      signals: ['policy-gate.status'],
      alerts: [],
    },
    exceptions: [],
    assurance: {
      targetLevel: 'A3',
      achievedLevel: 'A2',
      status: 'waived',
    },
    claims: [
      {
        id: 'manual-review',
        statement: 'Manual review is active.',
        status: 'waived',
        criticality: 'medium',
        artifactRefs: ['artifacts/runtime/manual-review.json'],
      },
      {
        id: 'no-negative-stock',
        statement: 'Inventory stock never becomes negative.',
        status: 'tested',
        criticality: 'high',
        artifactRefs: ['artifacts/testing/property-summary.json'],
      },
    ],
    assumptions: [],
    proofObligations: [
      {
        id: 'obl-no-negative-stock',
        claimId: 'no-negative-stock',
        method: 'tla',
        status: 'discharged',
        artifactRefs: ['artifacts/formal/no-negative-summary.json'],
      },
    ],
    counterexamples: [],
    trustBoundary: {
      outsideModel: [],
    },
    runtimeControls: {
      alerts: [],
      featureFlags: [],
    },
    waivers: [
      {
        owner: '@team-risk',
        expires: '2099-12-31',
        reason: 'Manual review control is active.',
        relatedClaimIds: ['manual-review'],
      },
    ],
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
            claimId: 'manual-review',
            owner: '@team-risk',
            expires: '2099-12-31',
            reason: 'Manual review control is active.',
          },
        ],
      },
    },
  });

  return { inputPath, policyDecisionPath };
}

describe('change-package validate', () => {
  it('passes in strict mode when required evidence is present', async () => {
    const workdir = await createWorkdir('change-package-validate-pass-');
    const inputPath = join(workdir, 'change-package.json');
    const outputJsonPath = join(workdir, 'validation.json');
    const outputMarkdownPath = join(workdir, 'validation.md');

    const fixture = await loadFixture();
    const evidence = (fixture.evidence as {
      items: Array<{ id: string; present: boolean }>;
      presentCount: number;
      missingCount: number;
    });
    evidence.items = evidence.items.map((item) => (item.id === 'verifyLiteSummary' ? { ...item, present: true } : item));
    evidence.presentCount = evidence.items.filter((item) => item.present).length;
    evidence.missingCount = evidence.items.length - evidence.presentCount;

    await writeFile(inputPath, `${JSON.stringify(fixture, null, 2)}\n`, 'utf8');

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', schemaPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--required-evidence', 'verifyLiteSummary',
      '--strict',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      result: string;
      errors: string[];
      warnings: string[];
    };
    expect(report.result).toBe('pass');
    expect(report.errors).toHaveLength(0);
    expect(report.warnings).toHaveLength(0);

    const markdown = await readFile(outputMarkdownPath, 'utf8');
    expect(markdown).toContain('Change Package Validation');
    expect(markdown).toContain('result: PASS');
  });

  it('fails in strict mode when required evidence is missing', async () => {
    const workdir = await createWorkdir('change-package-validate-fail-');
    const inputPath = join(workdir, 'change-package.json');
    const outputJsonPath = join(workdir, 'validation.json');
    const outputMarkdownPath = join(workdir, 'validation.md');

    const fixture = await loadFixture();
    const evidence = (fixture.evidence as {
      items: Array<{ id: string; present: boolean }>;
      presentCount: number;
      missingCount: number;
    });
    evidence.items = evidence.items.map((item) => (item.id === 'verifyLiteSummary' ? { ...item, present: false } : item));
    evidence.presentCount = evidence.items.filter((item) => item.present).length;
    evidence.missingCount = evidence.items.length - evidence.presentCount;

    await writeFile(inputPath, `${JSON.stringify(fixture, null, 2)}\n`, 'utf8');

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', schemaPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--required-evidence', 'verifyLiteSummary',
      '--strict',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(1);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      result: string;
      errors: string[];
      warnings: string[];
    };
    expect(report.result).toBe('fail');
    expect(report.errors.some((error) => error.includes('missing required evidence'))).toBe(true);
    expect(report.warnings).toHaveLength(0);
  });

  it('treats inferred high-risk as high-risk even when risk.isHighRisk is false', async () => {
    const workdir = await createWorkdir('change-package-validate-inferred-high-');
    const inputPath = join(workdir, 'change-package.json');
    const outputJsonPath = join(workdir, 'validation.json');
    const outputMarkdownPath = join(workdir, 'validation.md');

    const fixture = await loadFixture();
    const risk = fixture.risk as { selected: string; inferred: string; isHighRisk: boolean };
    risk.selected = 'risk:low';
    risk.inferred = 'risk:high';
    risk.isHighRisk = false;

    const evidence = fixture.evidence as {
      items: Array<{ id: string; present: boolean }>;
      presentCount: number;
      missingCount: number;
    };
    for (const item of evidence.items) {
      item.present = item.id === 'verifyLiteSummary';
    }
    evidence.presentCount = evidence.items.filter((item) => item.present).length;
    evidence.missingCount = evidence.items.length - evidence.presentCount;

    await writeFile(inputPath, `${JSON.stringify(fixture, null, 2)}\n`, 'utf8');

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', schemaPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--strict',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(1);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      result: string;
      evidence: {
        requiredEvidenceIds: string[];
        missingRequiredEvidence: Array<{ id: string }>;
      };
    };
    expect(report.result).toBe('fail');
    expect(report.evidence.requiredEvidenceIds).toContain('harnessHealth');
    expect(report.evidence.missingRequiredEvidence.some((item) => item.id === 'harnessHealth')).toBe(true);
  });

  it('passes v2 strict validation when artifactRefs and policy decision are consistent', async () => {
    const workdir = await createWorkdir('change-package-validate-v2-pass-');
    const outputJsonPath = join(workdir, 'validation.json');
    const outputMarkdownPath = join(workdir, 'validation.md');
    const { inputPath, policyDecisionPath } = await writeV2Fixture(workdir);

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', v2SchemaPath,
      '--artifact-root', workdir,
      '--policy-decision', policyDecisionPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--strict',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status, result.stderr || result.stdout).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      result: string;
      v2: {
        checked: boolean;
        claimCount: number;
        missingArtifactRefs: unknown[];
        policyDecision: { checked: boolean };
      };
    };
    expect(report.result).toBe('pass');
    expect(report.v2.checked).toBe(true);
    expect(report.v2.claimCount).toBe(2);
    expect(report.v2.missingArtifactRefs).toHaveLength(0);
    expect(report.v2.policyDecision.checked).toBe(true);

    const markdown = await readFile(outputMarkdownPath, 'utf8');
    expect(markdown).toContain('v2 consistency: claims=2, proofObligations=1, waivers=1');
  });

  it('uses payload evidence.artifactRoot for v2 artifactRefs when no CLI artifact root is provided', async () => {
    const workdir = await createWorkdir('change-package-validate-v2-payload-root-');
    const outputJsonPath = join(workdir, 'validation.json');
    const outputMarkdownPath = join(workdir, 'validation.md');
    const { inputPath } = await writeV2Fixture(workdir);
    const payload = JSON.parse(await readFile(inputPath, 'utf8')) as {
      evidence: { artifactRoot: string };
    };
    payload.evidence.artifactRoot = workdir;
    await writeJson(inputPath, payload);

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', v2SchemaPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--strict',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status, result.stderr || result.stdout).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      result: string;
      v2: { missingArtifactRefs: unknown[] };
    };
    expect(report.result).toBe('pass');
    expect(report.v2.missingArtifactRefs).toHaveLength(0);
  });

  it('fails v2 strict validation when artifactRefs and claim references are inconsistent', async () => {
    const workdir = await createWorkdir('change-package-validate-v2-fail-');
    const outputJsonPath = join(workdir, 'validation.json');
    const outputMarkdownPath = join(workdir, 'validation.md');
    const { inputPath } = await writeV2Fixture(workdir);
    const payload = JSON.parse(await readFile(inputPath, 'utf8')) as {
      claims: Array<{ artifactRefs: string[] }>;
      proofObligations: Array<{ claimId: string }>;
      waivers: Array<{ relatedClaimIds: string[] }>;
    };
    payload.claims[0].artifactRefs = ['artifacts/runtime/missing-manual-review.json'];
    payload.proofObligations[0].claimId = 'missing-claim';
    payload.waivers[0].relatedClaimIds = ['missing-waiver-claim'];
    await writeJson(inputPath, payload);

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', v2SchemaPath,
      '--artifact-root', workdir,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--strict',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(1);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      result: string;
      errors: string[];
    };
    expect(report.result).toBe('fail');
    expect(report.errors.some((error) => error.includes('proofObligations[0].claimId references missing claim'))).toBe(true);
    expect(report.errors.some((error) => error.includes('waivers[0].relatedClaimIds references missing claim'))).toBe(true);
    expect(report.errors.some((error) => error.includes('missing artifactRefs'))).toBe(true);
  });

  it('does not treat Windows absolute artifactRefs as URL schemes', async () => {
    const workdir = await createWorkdir('change-package-validate-v2-windows-ref-');
    const outputJsonPath = join(workdir, 'validation.json');
    const outputMarkdownPath = join(workdir, 'validation.md');
    const { inputPath } = await writeV2Fixture(workdir);
    const payload = JSON.parse(await readFile(inputPath, 'utf8')) as {
      claims: Array<{ artifactRefs: string[] }>;
    };
    payload.claims[0].artifactRefs = ['C:\\ae-framework\\missing-runtime-control.json'];
    await writeJson(inputPath, payload);

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', v2SchemaPath,
      '--artifact-root', workdir,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--strict',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(1);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      errors: string[];
    };
    expect(report.errors.some((error) => error.includes('C:\\ae-framework\\missing-runtime-control.json'))).toBe(true);
  });

  it('auto-detects the v2 schema when no schema override is provided', async () => {
    const workdir = await createWorkdir('change-package-validate-v2-autoschema-');
    const outputJsonPath = join(workdir, 'validation.json');
    const outputMarkdownPath = join(workdir, 'validation.md');
    const { inputPath } = await writeV2Fixture(workdir);

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--artifact-root', workdir,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--strict',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status, result.stderr || result.stdout).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      schema: { path: string };
    };
    expect(report.schema.path).toBe('schema/change-package-v2.schema.json');
  });
});
