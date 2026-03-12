import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const validateScript = join(process.cwd(), 'scripts/ci/validate-quality-scorecard.mjs');
const schemaPath = join(process.cwd(), 'schema/quality-scorecard.schema.json');

describe('validate-quality-scorecard CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'quality-scorecard-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('accepts valid quality scorecard payload', async () => {
    const summaryPath = join(workdir, 'quality-scorecard.json');
    const payload = {
      schemaVersion: 'quality-scorecard/v1',
      contractId: 'quality-scorecard.v1',
      generatedAt: '2026-03-12T00:00:00.000Z',
      metadata: {
        generatedAtUtc: '2026-03-12T00:00:00.000Z',
        generatedAtLocal: '2026-03-12T09:00:00.000+09:00',
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
      reportOnly: true,
      inputs: {
        verifyLiteSummary: { path: 'artifacts/verify-lite/verify-lite-run-summary.json', present: true, required: true },
        reportEnvelope: { path: 'artifacts/report-envelope.json', present: true, required: true },
        assuranceSummary: { path: null, present: false, required: false },
        harnessHealth: { path: null, present: false, required: false },
        policyGateSummary: { path: null, present: false, required: false },
        benchCompare: { path: null, present: false, required: false },
        formalSummary: null,
      },
      summary: {
        overallStatus: 'pass',
        overallScore: 100,
        availableDimensions: ['artifactIntegrity', 'executionHealth'],
        missingDimensions: ['assuranceCoverage', 'policyReadiness', 'performanceRegression'],
        blockerCount: 0,
      },
      dimensions: {
        artifactIntegrity: { status: 'pass', score: 100, weight: 25, summary: 'ok', details: {} },
        assuranceCoverage: { status: 'missing', score: null, weight: 25, summary: 'missing', details: {} },
        executionHealth: { status: 'pass', score: 100, weight: 25, summary: 'ok', details: {} },
        policyReadiness: { status: 'missing', score: null, weight: 15, summary: 'missing', details: {} },
        performanceRegression: { status: 'missing', score: null, weight: 10, summary: 'missing', details: {} },
      },
      blockers: [],
    };
    await writeFile(summaryPath, JSON.stringify(payload));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], { cwd: workdir });
    expect(result.status).toBe(0);
  });

  it('fails when blockers omit severity', async () => {
    const summaryPath = join(workdir, 'quality-scorecard.json');
    const payload = {
      schemaVersion: 'quality-scorecard/v1',
      contractId: 'quality-scorecard.v1',
      generatedAt: '2026-03-12T00:00:00.000Z',
      metadata: {
        generatedAtUtc: '2026-03-12T00:00:00.000Z',
        generatedAtLocal: '2026-03-12T09:00:00.000+09:00',
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
      reportOnly: true,
      inputs: {
        verifyLiteSummary: { path: 'artifacts/verify-lite/verify-lite-run-summary.json', present: true, required: true },
        reportEnvelope: { path: 'artifacts/report-envelope.json', present: true, required: true },
        assuranceSummary: { path: null, present: false, required: false },
        harnessHealth: { path: null, present: false, required: false },
        policyGateSummary: { path: null, present: false, required: false },
        benchCompare: { path: null, present: false, required: false },
        formalSummary: null,
      },
      summary: {
        overallStatus: 'fail',
        overallScore: 0,
        availableDimensions: ['artifactIntegrity'],
        missingDimensions: ['assuranceCoverage', 'executionHealth', 'policyReadiness', 'performanceRegression'],
        blockerCount: 1,
      },
      dimensions: {
        artifactIntegrity: { status: 'fail', score: 0, weight: 25, summary: 'fail', details: {} },
        assuranceCoverage: { status: 'missing', score: null, weight: 25, summary: 'missing', details: {} },
        executionHealth: { status: 'missing', score: null, weight: 25, summary: 'missing', details: {} },
        policyReadiness: { status: 'missing', score: null, weight: 15, summary: 'missing', details: {} },
        performanceRegression: { status: 'missing', score: null, weight: 10, summary: 'missing', details: {} },
      },
      blockers: [
        {
          dimension: 'artifactIntegrity',
          code: 'missing-required-artifact',
          message: 'required artifact missing',
          artifactPath: 'artifacts/report-envelope.json',
        },
      ],
    };
    await writeFile(summaryPath, JSON.stringify(payload));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], { cwd: workdir });
    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('/blockers/0');
  });

  it('fails when required input refs are marked missing', async () => {
    const summaryPath = join(workdir, 'quality-scorecard.json');
    const payload = {
      schemaVersion: 'quality-scorecard/v1',
      contractId: 'quality-scorecard.v1',
      generatedAt: '2026-03-12T00:00:00.000Z',
      metadata: {
        generatedAtUtc: '2026-03-12T00:00:00.000Z',
        generatedAtLocal: '2026-03-12T09:00:00.000+09:00',
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
      reportOnly: true,
      inputs: {
        verifyLiteSummary: { path: null, present: false, required: true },
        reportEnvelope: { path: 'artifacts/report-envelope.json', present: true, required: true },
        assuranceSummary: { path: null, present: false, required: false },
        harnessHealth: { path: null, present: false, required: false },
        policyGateSummary: { path: null, present: false, required: false },
        benchCompare: { path: null, present: false, required: false },
        formalSummary: null,
      },
      summary: {
        overallStatus: 'warn',
        overallScore: 70,
        availableDimensions: ['artifactIntegrity'],
        missingDimensions: ['assuranceCoverage', 'executionHealth', 'policyReadiness', 'performanceRegression'],
        blockerCount: 0,
      },
      dimensions: {
        artifactIntegrity: { status: 'warn', score: 70, weight: 25, summary: 'warn', details: {} },
        assuranceCoverage: { status: 'missing', score: null, weight: 25, summary: 'missing', details: {} },
        executionHealth: { status: 'missing', score: null, weight: 25, summary: 'missing', details: {} },
        policyReadiness: { status: 'missing', score: null, weight: 15, summary: 'missing', details: {} },
        performanceRegression: { status: 'missing', score: null, weight: 10, summary: 'missing', details: {} },
      },
      blockers: [],
    };
    await writeFile(summaryPath, JSON.stringify(payload));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], { cwd: workdir });
    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('/inputs/verifyLiteSummary');
  });
});
