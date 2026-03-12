import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/quality/build-quality-scorecard.mjs');

function createVerifyLiteSummary() {
  return {
    schemaVersion: '1.0.0',
    timestamp: '2026-03-12T00:00:00.000Z',
    metadata: {
      generatedAtUtc: '2026-03-12T00:00:00.000Z',
      generatedAtLocal: '2026-03-12T09:00:00.000+09:00',
      timezoneOffset: '+09:00',
      gitCommit: '0123456789abcdef0123456789abcdef01234567',
      branch: 'main',
      runner: { name: 'local', os: 'linux', arch: 'x64', ci: false },
      toolVersions: { node: 'v22.0.0' },
    },
    flags: {
      install: '',
      noFrozen: false,
      keepLintLog: false,
      enforceLint: false,
      runMutation: false,
    },
    steps: {
      install: { status: 'success', notes: null, retried: false },
      lint: { status: 'success' },
      build: { status: 'success' },
      conformanceReport: { status: 'success' },
    },
    artifacts: {
      lintSummary: null,
      lintLog: null,
      mutationSummary: null,
      mutationSurvivors: null,
      contextPackReportJson: null,
      contextPackReportMarkdown: null,
      contextPackFunctorReportJson: null,
      contextPackFunctorReportMarkdown: null,
      contextPackNaturalTransformationReportJson: null,
      contextPackNaturalTransformationReportMarkdown: null,
      contextPackProductCoproductReportJson: null,
      contextPackProductCoproductReportMarkdown: null,
      contextPackPhase5ReportJson: null,
      contextPackPhase5ReportMarkdown: null,
      conformanceSummary: 'artifacts/hermetic-reports/conformance/summary.json',
      conformanceSummaryMarkdown: null,
    },
  };
}

function createReportEnvelope() {
  return {
    schemaVersion: '1.0.0',
    source: 'verify-lite',
    generatedAt: '2026-03-12T00:00:00.000Z',
    traceCorrelation: {
      runId: 'demo-run',
      commit: 'HEAD',
      branch: 'feature/demo',
    },
    summary: {
      cases: 5,
      passed: 5,
    },
    artifacts: [
      {
        type: 'json',
        path: 'artifacts/verify-lite/verify-lite-run-summary.json',
      },
    ],
  };
}

function createAssuranceSummary() {
  return {
    schemaVersion: 'assurance-summary/v1',
    generatedAt: '2026-03-12T00:00:00.000Z',
    metadata: {
      generatedAtUtc: '2026-03-12T00:00:00.000Z',
      generatedAtLocal: '2026-03-12T09:00:00.000+09:00',
      timezoneOffset: '+09:00',
      gitCommit: '0123456789abcdef0123456789abcdef01234567',
      branch: 'main',
      runner: { name: 'local', os: 'linux', arch: 'x64', ci: false },
      toolVersions: { node: 'v22.0.0' },
    },
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
      satisfiedClaims: 1,
      warningClaims: 0,
      claimsMissingRequiredLanes: 0,
      claimsMissingRequiredEvidenceKinds: 0,
      unlinkedCounterexamples: 0,
      warningCount: 0,
    },
    laneCoverage: {
      spec: { requiredClaims: 1, observedClaims: 1 },
      behavior: { requiredClaims: 1, observedClaims: 1 },
      adversarial: { requiredClaims: 0, observedClaims: 0 },
      model: { requiredClaims: 1, observedClaims: 1 },
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
        counterexamples: { open: 0, resolved: 0, acceptedRisk: 0, total: 0 },
        independenceWarnings: [],
        status: 'satisfied',
        evidence: [],
      },
    ],
    warnings: [],
  };
}

function createFormalSummary(status = 'ok') {
  return {
    schemaVersion: 'formal-summary/v2',
    contractId: 'formal-summary.v2',
    tool: 'aggregate',
    status,
    ok: status === 'ok',
    generatedAtUtc: '2026-03-12T00:00:00.000Z',
    metadata: {
      generatedAtUtc: '2026-03-12T00:00:00.000Z',
      generatedAtLocal: '2026-03-12T09:00:00.000+09:00',
      timezoneOffset: '+09:00',
      gitCommit: '0123456789abcdef0123456789abcdef01234567',
      branch: 'main',
      runner: { name: 'local', os: 'linux', arch: 'x64', ci: false },
      toolVersions: { node: 'v22.0.0' },
    },
    results: [
      {
        name: 'conformance',
        status,
        code: status === 'ok' ? 0 : 1,
        durationMs: 10,
        logPath: 'artifacts/formal/formal-summary-v2.json',
        reason: status === 'ok' ? null : 'tool failed',
      },
    ],
  };
}

function createBenchCompare(overall = 'pass') {
  return {
    schemaVersion: 'bench-compare/v1',
    generatedAt: '2026-03-12T00:00:00.000Z',
    baseline: {
      path: 'artifacts/reference/benchmarks/bench.json',
      paths: ['artifacts/reference/benchmarks/bench.json'],
      runCount: 1,
      checksums: ['0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef'],
      metrics: { p95: 10, errorRate: 0, coldStartMs: 20, peakRssMb: 100 },
      throughputHz: 1000,
      taskCount: 1,
      reproducibility: { p95Cv: 0, throughputCv: 0, checksumMatchRate: 100 },
    },
    candidates: [
      {
        name: 'candidate',
        path: 'artifacts/bench-compare.json',
        metrics: { p95: 10, errorRate: 0, coldStartMs: 20, peakRssMb: 100 },
        throughputHz: 1000,
        taskCount: 1,
        comparison: {
          p95Ratio: 1,
          throughputRatio: 1,
          coldStartRatio: 1,
          peakRssRatio: 1,
          errorRateLimit: 0.5,
          errorRateDeltaPt: 0,
        },
        reproducibility: { p95Cv: 0, throughputCv: 0, checksumMatchRate: 100 },
        checks: {
          p95: overall === 'pass',
          throughput: overall === 'pass',
          errorRate: overall === 'pass',
          peakRss: overall === 'pass',
          coldStartReference: overall === 'pass',
          p95Cv: true,
          throughputCv: true,
          checksum: true,
        },
        overall,
      },
    ],
  };
}

describe.sequential('build-quality-scorecard', () => {
  it('builds a scorecard with missing optional dimensions', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-quality-scorecard-'));
    const verifyLitePath = join(sandbox, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json');
    const reportEnvelopePath = join(sandbox, 'artifacts', 'report-envelope.json');
    const assuranceSummaryPath = join(sandbox, 'artifacts', 'assurance', 'assurance-summary.json');
    const formalSummaryPath = join(sandbox, 'artifacts', 'formal', 'formal-summary-v2.json');
    const outJson = join(sandbox, 'artifacts', 'quality', 'quality-scorecard.json');
    const outMd = join(sandbox, 'artifacts', 'quality', 'quality-scorecard.md');

    try {
      mkdirSync(join(sandbox, 'artifacts', 'verify-lite'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'assurance'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'formal'), { recursive: true });
      writeFileSync(verifyLitePath, `${JSON.stringify(createVerifyLiteSummary(), null, 2)}\n`);
      writeFileSync(reportEnvelopePath, `${JSON.stringify(createReportEnvelope(), null, 2)}\n`);
      writeFileSync(assuranceSummaryPath, `${JSON.stringify(createAssuranceSummary(), null, 2)}\n`);
      writeFileSync(formalSummaryPath, `${JSON.stringify(createFormalSummary(), null, 2)}\n`);

      const result = spawnSync('node', [
        scriptPath,
        '--verify-lite-summary', verifyLitePath,
        '--report-envelope', reportEnvelopePath,
        '--assurance-summary', assuranceSummaryPath,
        '--formal-summary', formalSummaryPath,
        '--output-json', outJson,
        '--output-md', outMd,
      ], { cwd: sandbox, encoding: 'utf8', timeout: 120_000 });

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const payload = JSON.parse(readFileSync(outJson, 'utf8')) as {
        summary: { overallStatus: string; missingDimensions: string[] };
        dimensions: { performanceRegression: { status: string } };
        blockers: Array<{ code: string }>;
      };
      const markdown = readFileSync(outMd, 'utf8');

      expect(payload.summary.overallStatus).toBe('pass');
      expect(payload.dimensions.performanceRegression.status).toBe('missing');
      expect(payload.summary.missingDimensions).toContain('policyReadiness');
      expect(payload.blockers).toHaveLength(0);
      expect(markdown).toContain('# Quality Scorecard');
      expect(markdown).toContain('performanceRegression: missing');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('reports blockers when optional summaries indicate failures', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-quality-scorecard-fail-'));
    const verifyLitePath = join(sandbox, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json');
    const reportEnvelopePath = join(sandbox, 'artifacts', 'report-envelope.json');
    const harnessHealthPath = join(sandbox, 'artifacts', 'ci', 'harness-health.json');
    const benchComparePath = join(sandbox, 'artifacts', 'bench-compare.json');
    const outJson = join(sandbox, 'artifacts', 'quality', 'quality-scorecard.json');

    try {
      mkdirSync(join(sandbox, 'artifacts', 'verify-lite'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'ci'), { recursive: true });
      writeFileSync(verifyLitePath, `${JSON.stringify(createVerifyLiteSummary(), null, 2)}\n`);
      writeFileSync(reportEnvelopePath, `${JSON.stringify(createReportEnvelope(), null, 2)}\n`);
      writeFileSync(
        harnessHealthPath,
        `${JSON.stringify({ ...JSON.parse(readFileSync(resolve(repoRoot, 'fixtures/ci/sample.harness-health.json'), 'utf8')), severity: 'critical' }, null, 2)}\n`,
      );
      writeFileSync(benchComparePath, `${JSON.stringify(createBenchCompare('fail'), null, 2)}\n`);

      const result = spawnSync('node', [
        scriptPath,
        '--verify-lite-summary', verifyLitePath,
        '--report-envelope', reportEnvelopePath,
        '--harness-health', harnessHealthPath,
        '--bench-compare', benchComparePath,
        '--output-json', outJson,
      ], { cwd: sandbox, encoding: 'utf8', timeout: 120_000 });

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const payload = JSON.parse(readFileSync(outJson, 'utf8')) as {
        summary: { overallStatus: string };
        blockers: Array<{ code: string }>;
      };
      expect(payload.summary.overallStatus).toBe('fail');
      expect(payload.blockers.map((entry) => entry.code)).toContain('harness-health-critical');
      expect(payload.blockers.map((entry) => entry.code)).toContain('bench-compare-regression');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('downgrades execution health when formal summary is skipped', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-quality-scorecard-formal-skipped-'));
    const verifyLitePath = join(sandbox, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json');
    const reportEnvelopePath = join(sandbox, 'artifacts', 'report-envelope.json');
    const assuranceSummaryPath = join(sandbox, 'artifacts', 'assurance', 'assurance-summary.json');
    const formalSummaryPath = join(sandbox, 'artifacts', 'formal', 'formal-summary-v2.json');
    const outJson = join(sandbox, 'artifacts', 'quality', 'quality-scorecard.json');

    try {
      mkdirSync(join(sandbox, 'artifacts', 'verify-lite'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'assurance'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'formal'), { recursive: true });
      writeFileSync(verifyLitePath, `${JSON.stringify(createVerifyLiteSummary(), null, 2)}\n`);
      writeFileSync(reportEnvelopePath, `${JSON.stringify(createReportEnvelope(), null, 2)}\n`);
      writeFileSync(assuranceSummaryPath, `${JSON.stringify(createAssuranceSummary(), null, 2)}\n`);
      writeFileSync(formalSummaryPath, `${JSON.stringify(createFormalSummary('skipped'), null, 2)}\n`);

      const result = spawnSync('node', [
        scriptPath,
        '--verify-lite-summary', verifyLitePath,
        '--report-envelope', reportEnvelopePath,
        '--assurance-summary', assuranceSummaryPath,
        '--formal-summary', formalSummaryPath,
        '--output-json', outJson,
      ], { cwd: sandbox, encoding: 'utf8', timeout: 120_000 });

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const payload = JSON.parse(readFileSync(outJson, 'utf8')) as {
        summary: { overallStatus: string };
        dimensions: { executionHealth: { status: string } };
        blockers: Array<{ code: string; severity: string }>;
      };

      expect(payload.dimensions.executionHealth.status).toBe('warn');
      expect(payload.summary.overallStatus).toBe('warn');
      expect(payload.blockers).toContainEqual(expect.objectContaining({
        code: 'formal-summary-not-executed',
        severity: 'warn',
      }));
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
