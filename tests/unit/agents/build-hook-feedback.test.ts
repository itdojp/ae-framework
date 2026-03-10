import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { buildHookFeedbackArtifact } from '../../../scripts/agents/build-hook-feedback.mjs';

const scriptPath = resolve(process.cwd(), 'scripts/agents/build-hook-feedback.mjs');
const schemaPath = resolve(process.cwd(), 'schema/hook-feedback.schema.json');

const schema = JSON.parse(await readFile(schemaPath, 'utf8')) as Record<string, unknown>;
const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);
const validate = ajv.compile(schema);

describe('build-hook-feedback CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'hook-feedback-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  async function writeJson(relativePath: string, payload: unknown) {
    const fullPath = join(workdir, relativePath);
    await mkdir(dirname(fullPath), { recursive: true });
    await writeFile(fullPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
    return fullPath;
  }

  function runBuild(extraArgs: string[] = []) {
    const outputJsonPath = join(workdir, 'artifacts', 'agents', 'hook-feedback.json');
    const outputMdPath = join(workdir, 'artifacts', 'agents', 'hook-feedback.md');
    const result = spawnSync(process.execPath, [
      scriptPath,
      '--output-json',
      outputJsonPath,
      '--output-md',
      outputMdPath,
      ...extraArgs,
    ], {
      cwd: workdir,
    });
    return { result, outputJsonPath, outputMdPath };
  }

  it('builds blocked feedback with actionable next actions and repro commands', async () => {
    await writeJson('artifacts/verify-lite/verify-lite-run-summary.json', {
      schemaVersion: '1.0.0',
      timestamp: '2026-03-09T00:00:00.000Z',
      metadata: { generatedAt: '2026-03-09T00:00:00.000Z', generator: 'test', toolVersions: {} },
      flags: { install: '', noFrozen: false, keepLintLog: false, enforceLint: false, runMutation: false },
      steps: {
        lint: { status: 'failure' },
        build: { status: 'success' },
      },
      traceability: {
        status: 'failure',
        missingCount: 2,
        matrixPath: 'artifacts/traceability/matrix.json',
        notes: '2 links missing',
      },
      artifacts: {
        lintSummary: null,
        lintLog: null,
        mutationSummary: null,
        mutationSurvivors: null,
        conformanceSummary: null,
        conformanceSummaryMarkdown: null,
      },
    });
    await writeJson('artifacts/ci/harness-health.json', {
      schemaVersion: 'harness-health/v1',
      generatedAt: '2026-03-09T00:00:00.000Z',
      severity: 'critical',
      reasons: ['Testing harness: 1 failing reproducibility records.'],
      recommendedLabels: ['run-ci-extended'],
      recommendedContextChanges: [
        {
          file: 'spec/context-pack/functor-map.json',
          changeType: 'add',
          targetId: 'ReserveInventory',
          suggestedCommand: 'pnpm run context-pack:verify-functor',
        },
      ],
      reproducibleHints: [
        { gate: 'testingHarness', command: 'pnpm run test:ci:extended' },
      ],
      gates: {},
    });
    await writeJson('artifacts/change-package/change-package.json', {
      schemaVersion: 'change-package/v1',
      risk: {
        selected: 'risk:high',
        missingRequiredLabels: ['run-ci-extended'],
      },
      evidence: {
        items: [
          {
            id: 'verifyLiteSummary',
            path: 'artifacts/verify-lite/verify-lite-run-summary.json',
            description: 'verify-lite run summary',
            present: true,
          },
        ],
      },
      reproducibility: {
        commands: ['pnpm run verify:lite', 'pnpm run test:ci:extended'],
      },
      exceptions: [
        { code: 'missing-required-labels', message: 'Missing required labels: run-ci-extended' },
      ],
    });
    await writeJson('artifacts/context-pack/context-pack-suggestions.json', {
      schemaVersion: 'context-pack-suggestions/v1',
      generatedAt: '2026-03-09T00:00:00.000Z',
      status: 'fail',
      recommendedContextChanges: [
        {
          file: 'spec/context-pack/functor-map.json',
          changeType: 'add',
          targetId: 'ReserveInventory',
          suggestedCommand: 'pnpm run context-pack:verify-functor',
        },
      ],
    });
    await writeJson('artifacts/assurance/assurance-summary.json', {
      schemaVersion: 'assurance-summary/v1',
      generatedAt: '2026-03-09T00:00:00.000Z',
      metadata: {},
      inputs: {
        assuranceProfile: 'fixtures/assurance/sample.assurance-profile.json',
        contextPacks: [],
        verifyLiteSummary: 'artifacts/verify-lite/verify-lite-run-summary.json',
        formalSummaries: [],
        conformanceReport: null,
        counterexamples: [],
        evidenceManifests: [],
      },
      summary: {
        claimCount: 1,
        satisfiedClaims: 0,
        warningClaims: 1,
        claimsMissingRequiredLanes: 1,
        claimsMissingRequiredEvidenceKinds: 1,
        unlinkedCounterexamples: 1,
        warningCount: 2,
      },
      laneCoverage: {
        spec: { requiredClaims: 1, observedClaims: 1 },
        behavior: { requiredClaims: 1, observedClaims: 0 },
        adversarial: { requiredClaims: 0, observedClaims: 0 },
        model: { requiredClaims: 1, observedClaims: 0 },
        proof: { requiredClaims: 0, observedClaims: 0 },
        runtime: { requiredClaims: 0, observedClaims: 0 },
      },
      claims: [
        {
          claimId: 'inventory-safe',
          statement: 'inventory remains safe',
          criticality: 'high',
          targetLevel: 'A2',
          minIndependentSources: 2,
          observedIndependentSources: 1,
          requiredLanes: ['spec', 'behavior', 'model'],
          observedLanes: ['spec'],
          missingLanes: ['behavior', 'model'],
          requiredEvidenceKinds: ['property'],
          observedEvidenceKinds: [],
          missingEvidenceKinds: ['property'],
          counterexamples: { open: 1, resolved: 0, acceptedRisk: 0, total: 1 },
          independenceWarnings: [],
          status: 'warning',
          evidence: [],
        },
      ],
      warnings: [],
    });
    await writeJson('artifacts/e2e/ui-e2e-summary.json', {
      schemaVersion: 'ui-e2e-summary/v1',
      generatedAt: '2026-03-09T00:00:00.000Z',
      status: 'error',
      baseUrl: 'http://127.0.0.1:3100',
      summary: { total: 1, passed: 0, failed: 1, skipped: 0, ariaSnapshotCount: 0 },
      scenarios: [
        {
          id: 'semantic-form',
          title: 'semantic form',
          status: 'fail',
          startedAt: '2026-03-09T00:00:00.000Z',
          finishedAt: '2026-03-09T00:00:01.000Z',
          durationMs: 1000,
          url: 'http://127.0.0.1:3100/ja/e2e/semantic-form',
          semanticChecks: ['submit status exposed'],
          diagnostics: [{ kind: 'semantic', message: 'status missing', ariaSnapshotPath: null }],
          ariaSnapshotPath: null,
        },
      ],
      artifacts: {
        ariaSnapshotsDir: 'artifacts/e2e/ui-aria-snapshots',
        adapterSummaryPath: 'artifacts/e2e/summary.json',
      },
    });

    const { result, outputJsonPath, outputMdPath } = runBuild();
    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      status: string;
      nextActions: string[];
      reproCommands: string[];
      evidence: Array<{ id: string }>;
      blockingReasons: string[];
      source: { assuranceSummaryPath: string | null; uiE2ESummaryPath: string | null };
    };
    expect(validate(report), JSON.stringify(validate.errors)).toBe(true);
    expect(report.status).toBe('blocked');
    expect(report.blockingReasons.some((entry) => entry.includes('Missing required labels'))).toBe(true);
    expect(report.blockingReasons.some((entry) => entry.includes('Assurance summary warnings'))).toBe(true);
    expect(report.blockingReasons.some((entry) => entry.includes('UI semantic E2E status=error'))).toBe(true);
    expect(report.nextActions.some((entry) => entry.includes('fix failing verify-lite steps'))).toBe(true);
    expect(report.nextActions.some((entry) => entry.includes('run-ci-extended'))).toBe(true);
    expect(report.nextActions.some((entry) => entry.includes('pnpm run verify:assurance'))).toBe(true);
    expect(report.nextActions.some((entry) => entry.includes('pnpm run ui-e2e:semantic'))).toBe(true);
    expect(report.reproCommands).toContain('pnpm run verify:lite');
    expect(report.reproCommands).toContain('pnpm run test:ci:extended');
    expect(report.reproCommands).toContain('pnpm run context-pack:verify-functor');
    expect(report.reproCommands).toContain('pnpm run verify:assurance');
    expect(report.reproCommands).toContain('pnpm run ui-e2e:semantic');
    expect(report.evidence.some((entry) => entry.id === 'harnessHealth')).toBe(true);
    expect(report.evidence.some((entry) => entry.id === 'assuranceSummary')).toBe(true);
    expect(report.evidence.some((entry) => entry.id === 'uiE2ESummary')).toBe(true);
    expect(report.source.assuranceSummaryPath).toBe('artifacts/assurance/assurance-summary.json');
    expect(report.source.uiE2ESummaryPath).toBe('artifacts/e2e/ui-e2e-summary.json');

    const markdown = await readFile(outputMdPath, 'utf8');
    expect(markdown).toContain('# Hook Feedback');
    expect(markdown).toContain('## Repro commands');
    expect(markdown).toContain('assurance-summary');
    expect(markdown).toContain('ui-e2e-summary');
  });

  it('builds warn feedback and falls back to verify-lite command when no repro command is present', async () => {
    await writeJson('artifacts/verify-lite/verify-lite-run-summary.json', {
      schemaVersion: '1.0.0',
      timestamp: '2026-03-09T00:00:00.000Z',
      metadata: { generatedAt: '2026-03-09T00:00:00.000Z', generator: 'test', toolVersions: {} },
      flags: { install: '', noFrozen: false, keepLintLog: false, enforceLint: false, runMutation: false },
      steps: {
        lint: { status: 'pending' },
        build: { status: 'success' },
      },
      artifacts: {
        lintSummary: null,
        lintLog: null,
        mutationSummary: null,
        mutationSurvivors: null,
        conformanceSummary: null,
        conformanceSummaryMarkdown: null,
      },
    });
    await writeJson('artifacts/ci/harness-health.json', {
      schemaVersion: 'harness-health/v1',
      generatedAt: '2026-03-09T00:00:00.000Z',
      severity: 'warn',
      reasons: ['Testing harness: pending checks.'],
      recommendedLabels: [],
      recommendedContextChanges: [],
      reproducibleHints: [],
      gates: {},
    });
    await writeJson('artifacts/change-package/change-package.json', {
      schemaVersion: 'change-package/v1',
      evidence: { items: [] },
      reproducibility: { commands: [] },
      exceptions: [],
      risk: { selected: 'risk:low', missingRequiredLabels: [] },
    });

    const { result, outputJsonPath } = runBuild();
    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      status: string;
      reproCommands: string[];
      nextActions: string[];
      source: { contextPackSuggestionsPath: string | null };
    };
    expect(validate(report), JSON.stringify(validate.errors)).toBe(true);
    expect(report.status).toBe('warn');
    expect(report.reproCommands).toEqual(['pnpm run verify:lite']);
    expect(report.nextActions[0]).toContain('incomplete verify-lite steps');
    expect(report.source.contextPackSuggestionsPath).toBeNull();
    expect(report.source.assuranceSummaryPath).toBeNull();
    expect(report.source.uiE2ESummaryPath).toBeNull();
  });

  it('merges canonical evidence status and includes harness suggested commands in repro commands', async () => {
    await writeJson('artifacts/verify-lite/verify-lite-run-summary.json', {
      schemaVersion: '1.0.0',
      timestamp: '2026-03-09T00:00:00.000Z',
      metadata: { generatedAt: '2026-03-09T00:00:00.000Z', generator: 'test', toolVersions: {} },
      flags: { install: '', noFrozen: false, keepLintLog: false, enforceLint: false, runMutation: false },
      steps: {
        lint: { status: 'failure' },
      },
      artifacts: {},
    });
    await writeJson('artifacts/ci/harness-health.json', {
      schemaVersion: 'harness-health/v1',
      generatedAt: '2026-03-09T00:00:00.000Z',
      severity: 'warn',
      reasons: [],
      recommendedLabels: [],
      recommendedContextChanges: [
        {
          file: 'spec/context-pack/functor-map.json',
          changeType: 'update',
          targetId: 'ReserveInventory',
          suggestedCommand: 'pnpm run context-pack:verify-functor',
        },
      ],
      reproducibleHints: [],
      gates: {},
    });
    await writeJson('artifacts/change-package/change-package.json', {
      schemaVersion: 'change-package/v1',
      risk: { selected: 'risk:low', missingRequiredLabels: [] },
      evidence: {
        items: [
          {
            id: 'verifyLiteSummary',
            path: 'artifacts/verify-lite/verify-lite-run-summary.json',
            description: 'verify-lite run summary',
            present: true,
            status: null,
          },
        ],
      },
      reproducibility: { commands: [] },
      exceptions: [],
    });

    const { result, outputJsonPath } = runBuild();
    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      reproCommands: string[];
      evidence: Array<{ path: string; status: string | null }>;
    };
    const verifyEvidence = report.evidence.find((entry) => entry.path === 'artifacts/verify-lite/verify-lite-run-summary.json');
    expect(verifyEvidence?.status).toBe('failure');
    expect(report.reproCommands).toContain('pnpm run context-pack:verify-functor');
  });

  it('builds warn feedback when harness-health and change-package are missing', async () => {
    await writeJson('artifacts/verify-lite/verify-lite-run-summary.json', {
      schemaVersion: '1.0.0',
      timestamp: '2026-03-09T00:00:00.000Z',
      metadata: { generatedAt: '2026-03-09T00:00:00.000Z', generator: 'test', toolVersions: {} },
      flags: { install: '', noFrozen: false, keepLintLog: false, enforceLint: false, runMutation: false },
      steps: {
        lint: { status: 'success' },
        build: { status: 'success' },
      },
      artifacts: {
        lintSummary: null,
        lintLog: null,
        mutationSummary: null,
        mutationSurvivors: null,
        conformanceSummary: null,
        conformanceSummaryMarkdown: null,
      },
    });

    const { result, outputJsonPath, outputMdPath } = runBuild();
    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      status: string;
      blockingReasons: string[];
      nextActions: string[];
      reproCommands: string[];
      evidence: Array<{ id: string; present: boolean; status: string | null; path: string }>;
      source: {
        verifyLiteSummaryPath: string;
        harnessHealthPath: string | null;
        changePackagePath: string | null;
        contextPackSuggestionsPath: string | null;
        assuranceSummaryPath: string | null;
        uiE2ESummaryPath: string | null;
      };
    };
    expect(validate(report), JSON.stringify(validate.errors)).toBe(true);
    expect(report.status).toBe('warn');
    expect(report.blockingReasons).toContain('Missing artifact: harness-health');
    expect(report.blockingReasons).toContain('Missing artifact: change-package');
    expect(report.nextActions).toContain(
      'Generate `artifacts/ci/harness-health.json` with `node scripts/ci/build-harness-health.mjs` when gate-level guidance is needed.',
    );
    expect(report.nextActions).toContain(
      'Generate `artifacts/change-package/change-package.json` with `pnpm run change-package:generate` when risk/evidence packaging is needed.',
    );
    expect(report.reproCommands).toContain('node scripts/ci/build-harness-health.mjs');
    expect(report.reproCommands).toContain('pnpm run change-package:generate');
    expect(report.source.verifyLiteSummaryPath).toBe('artifacts/verify-lite/verify-lite-run-summary.json');
    expect(report.source.harnessHealthPath).toBeNull();
    expect(report.source.changePackagePath).toBeNull();
    expect(report.source.contextPackSuggestionsPath).toBeNull();
    expect(report.source.assuranceSummaryPath).toBeNull();
    expect(report.source.uiE2ESummaryPath).toBeNull();
    expect(report.evidence).toEqual(
      expect.arrayContaining([
        expect.objectContaining({
          id: 'harnessHealth',
          path: 'artifacts/ci/harness-health.json',
          present: false,
          status: 'missing',
        }),
        expect.objectContaining({
          id: 'changePackage',
          path: 'artifacts/change-package/change-package.json',
          present: false,
          status: 'missing',
        }),
      ]),
    );

    const markdown = await readFile(outputMdPath, 'utf8');
    expect(markdown).toContain('harness-health: `n/a`');
    expect(markdown).toContain('change-package: `n/a`');
  });

  it('keeps missing core evidence entries when buildHookFeedbackArtifact uses default evidenceSource', () => {
    const artifact = buildHookFeedbackArtifact({
      verifyLiteSummary: {
        schemaVersion: '1.0.0',
        steps: {
          lint: { status: 'success' },
          build: { status: 'success' },
        },
      },
      harnessHealth: null,
      changePackage: null,
      contextPackSuggestions: null,
      assuranceSummary: null,
      uiE2ESummary: null,
      source: {
        verifyLiteSummaryPath: 'artifacts/verify-lite/verify-lite-run-summary.json',
        harnessHealthPath: null,
        changePackagePath: null,
        contextPackSuggestionsPath: null,
        assuranceSummaryPath: null,
        uiE2ESummaryPath: null,
      },
      now: '2026-03-10T12:00:00.000Z',
    });

    expect(validate(artifact), JSON.stringify(validate.errors)).toBe(true);
    expect(artifact.evidence).toEqual(
      expect.arrayContaining([
        expect.objectContaining({
          id: 'harnessHealth',
          path: 'artifacts/ci/harness-health.json',
          present: false,
          status: 'missing',
        }),
        expect.objectContaining({
          id: 'changePackage',
          path: 'artifacts/change-package/change-package.json',
          present: false,
          status: 'missing',
        }),
      ]),
    );
  });
});
