import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/assurance/aggregate-lanes.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

const writeJson = (targetPath: string, payload: unknown) => {
  writeFileSync(targetPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
};

const createVerifyLiteSummary = (overrides = {}) => ({
  schemaVersion: '1.0.0',
  timestamp: '2026-03-08T09:00:00.000Z',
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
  flags: {
    install: '',
    noFrozen: false,
    keepLintLog: false,
    enforceLint: false,
    runMutation: true,
  },
  steps: {
    install: { status: 'success', notes: null, retried: false },
    contextPackValidation: { status: 'success', notes: null },
    contextPackProductCoproductValidation: { status: 'success', notes: null },
    conformanceReport: { status: 'success', notes: null },
  },
  artifacts: {
    lintSummary: null,
    lintLog: null,
    mutationSummary: 'artifacts/testing/mutation-summary.json',
    mutationSurvivors: 'artifacts/testing/mutation-survivors.json',
    contextPackReportJson: 'artifacts/context-pack/context-pack-validate-report.json',
    contextPackReportMarkdown: null,
    contextPackFunctorReportJson: null,
    contextPackFunctorReportMarkdown: null,
    contextPackNaturalTransformationReportJson: null,
    contextPackNaturalTransformationReportMarkdown: null,
    contextPackProductCoproductReportJson: 'artifacts/context-pack/context-pack-product-coproduct-report.json',
    contextPackProductCoproductReportMarkdown: null,
    contextPackPhase5ReportJson: null,
    contextPackPhase5ReportMarkdown: null,
    conformanceSummary: 'artifacts/hermetic-reports/conformance/summary.json',
    conformanceSummaryMarkdown: null,
  },
  ...overrides,
});

const createFormalSummary = () => ({
  schemaVersion: 'formal-summary/v2',
  contractId: 'formal-summary.v2',
  tool: 'aggregate',
  status: 'ok',
  ok: true,
  generatedAtUtc: '2026-03-08T09:05:00.000Z',
  metadata: {
    generatedAtUtc: '2026-03-08T09:05:00.000Z',
    generatedAtLocal: '2026-03-08T18:05:00.000+09:00',
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
  results: [
    {
      name: 'conformance',
      status: 'ok',
      code: 0,
      durationMs: 15,
      logPath: 'artifacts/hermetic-reports/conformance/summary.json',
      reason: null,
    },
    {
      name: 'lean',
      status: 'ok',
      code: 0,
      durationMs: 7,
      logPath: 'artifacts/formal/lean-output.txt',
      reason: null,
    },
  ],
});

const createConformanceReport = () => ({
  schemaVersion: '1.0.0',
  generatedAt: '2026-03-08T09:06:00.000Z',
  status: 'success',
  runsAnalyzed: 2,
  statusBreakdown: { pass: 2, fail: 0, skip: 0, error: 0, timeout: 0 },
  totals: {
    rulesExecuted: 4,
    rulesPassed: 4,
    rulesFailed: 0,
    rulesErrored: 0,
    rulesSkipped: 0,
    totalViolations: 0,
    uniqueRules: 4,
    uniqueViolationRules: 0,
  },
  severityTotals: { critical: 0, major: 0, minor: 0, info: 0, warning: 0 },
  categoryTotals: {
    data_validation: 0,
    api_contract: 0,
    business_logic: 0,
    security_policy: 0,
    performance_constraint: 0,
    resource_usage: 0,
    state_invariant: 0,
    behavioral_constraint: 0,
    integration_requirement: 0,
    compliance_rule: 0,
  },
  severityTrends: [],
  topViolations: [],
  inputs: [],
});

const createCounterexample = (overrides = {}) => ({
  schemaVersion: '1.0.0',
  backend: 'tlc',
  spec: 'spec/tla/Inventory.tla',
  claimIds: ['no-negative-stock'],
  morphismIds: ['ReserveInventory'],
  triageStatus: 'resolved',
  replayCommand: 'pnpm run model-check -- --spec spec/tla/Inventory.tla',
  suggestedContextChanges: {
    summary: 'Strengthen reservation precondition.',
    contextPackSuggestionPath: 'artifacts/context-pack/context-pack-suggestions.json',
  },
  violated: {
    kind: 'INVARIANT',
    name: 'NoNegativeStock',
    message: 'stock dropped below zero',
  },
  trace: [
    {
      index: 0,
      state: {
        stock: 0,
      },
    },
  ],
  ...overrides,
});

const createEvidenceManifest = (entries: Array<Record<string, unknown>>) => ({
  schemaVersion: 'assurance-evidence-manifest/v1',
  entries,
});

const runScript = (args: string[], cwd = repoRoot) =>
  spawnSync('node', [scriptPath, ...args], {
    cwd,
    encoding: 'utf8',
    timeout: 120_000,
  });

describe.sequential('assurance aggregate lanes script', () => {
  it('parses arguments and aggregates observed lanes with supplemental evidence', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs(['--assurance-profile', 'fixtures/assurance/sample.assurance-profile.json'])).toMatchObject({
      assuranceProfile: 'fixtures/assurance/sample.assurance-profile.json',
      outputJson: 'artifacts/assurance/assurance-summary.json',
      outputMd: 'artifacts/assurance/assurance-summary.md',
    });
    expect(() => mod.parseArgs(['--assurance-profile'])).toThrow('--assurance-profile requires a value');

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-assurance-aggregate-success-'));
    const verifyLitePath = join(sandbox, 'verify-lite-run-summary.json');
    const formalSummaryPath = join(sandbox, 'formal-summary-v2.json');
    const conformanceReportPath = join(sandbox, 'conformance-report.json');
    const counterexamplePath = join(sandbox, 'counterexample.json');
    const evidenceManifestPath = join(sandbox, 'evidence-manifest.json');
    const outputJson = join(sandbox, 'assurance-summary.json');
    const outputMd = join(sandbox, 'assurance-summary.md');

    try {
      writeJson(verifyLitePath, createVerifyLiteSummary());
      writeJson(formalSummaryPath, createFormalSummary());
      writeJson(conformanceReportPath, createConformanceReport());
      writeJson(counterexamplePath, createCounterexample());
      writeJson(
        evidenceManifestPath,
        createEvidenceManifest([
          {
            lane: 'behavior',
            kind: 'property',
            sourceKind: 'source-derived',
            claimIds: ['no-negative-stock'],
            artifactPath: 'artifacts/testing/property-summary.json',
            generatorLineage: 'property-harness',
            detail: 'property suite passed',
          },
          {
            lane: 'runtime',
            kind: 'runtime-alert',
            sourceKind: 'runtime-derived',
            claimIds: ['no-negative-stock'],
            artifactPath: 'artifacts/runtime/alerts/no-negative-stock.json',
            generatorLineage: 'runtime-guard',
            detail: 'runtime alert configured',
          },
        ]),
      );

      const result = runScript([
        '--assurance-profile',
        'fixtures/assurance/sample.assurance-profile.json',
        '--context-pack',
        'fixtures/context-pack/sample.context-pack.json',
        '--verify-lite-summary',
        verifyLitePath,
        '--formal-summary',
        formalSummaryPath,
        '--conformance-report',
        conformanceReportPath,
        '--counterexample',
        counterexamplePath,
        '--evidence-manifest',
        evidenceManifestPath,
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('[assurance] wrote summary');

      const summary = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(summary.schemaVersion).toBe('assurance-summary/v1');
      expect(summary.summary.claimCount).toBe(1);
      expect(summary.summary.warningCount).toBe(0);
      expect(summary.claims[0]).toMatchObject({
        claimId: 'no-negative-stock',
        status: 'satisfied',
        observedLanes: ['adversarial', 'behavior', 'model', 'proof', 'runtime', 'spec'],
        missingLanes: [],
        observedEvidenceKinds: expect.arrayContaining(['property', 'product-coproduct', 'counterexample-closed']),
      });
      expect(summary.claims[0].counterexamples).toMatchObject({
        open: 0,
        resolved: 1,
        acceptedRisk: 0,
        total: 1,
      });
      expect(summary.laneCoverage.proof.observedClaims).toBe(1);
      expect(readFileSync(outputMd, 'utf8')).toContain('## Claim status');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('reports missing spec-derived evidence and unresolved critical counterexamples', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-assurance-aggregate-warning-'));
    const counterexamplePath = join(sandbox, 'counterexample.json');
    const evidenceManifestPath = join(sandbox, 'evidence-manifest.json');
    const outputJson = join(sandbox, 'assurance-summary.json');

    try {
      writeJson(
        counterexamplePath,
        createCounterexample({
          backend: 'property',
          triageStatus: 'open',
        }),
      );
      writeJson(
        evidenceManifestPath,
        createEvidenceManifest([
          {
            lane: 'behavior',
            kind: 'property',
            sourceKind: 'source-derived',
            claimIds: ['no-negative-stock'],
            artifactPath: 'artifacts/testing/property-summary.json',
            generatorLineage: 'property-harness',
          },
        ]),
      );

      const result = runScript([
        '--assurance-profile',
        'fixtures/assurance/sample.assurance-profile.json',
        '--counterexample',
        counterexamplePath,
        '--evidence-manifest',
        evidenceManifestPath,
        '--output-json',
        outputJson,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(summary.summary.warningCount).toBeGreaterThan(0);
      expect(summary.claims[0].status).toBe('warning');
      expect(summary.claims[0].independenceWarnings).toEqual(
        expect.arrayContaining([
          'missing-spec-derived-evidence',
          'unresolved-critical-counterexample',
          'insufficient-independent-lanes',
        ]),
      );
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
