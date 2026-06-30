import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  compareJudgmentArtifacts,
  parseArgs,
} from '../../scripts/quality/compare-judgment-artifacts.mjs';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/quality/compare-judgment-artifacts.mjs');
const outputDir = resolve(repoRoot, '.codex-local/tmp/variance-report-test');

function resetOutputDir() {
  rmSync(outputDir, { recursive: true, force: true });
  mkdirSync(outputDir, { recursive: true });
}

describe('compare-judgment-artifacts', () => {
  it('treats repeated runs with the same inputs as a stable normalized judgment', () => {
    const report = compareJudgmentArtifacts(parseArgs([
      '--baseline',
      'fixtures/variance/run-a.judgment.json',
      '--candidate',
      'fixtures/variance/run-b.same-inputs.judgment.json',
    ]));

    expect(report.summary.status).toBe('stable');
    expect(report.normalizedJudgment.match).toBe(true);
    expect(report.findings).toHaveLength(0);
    expect(report.summary.expectedDifferenceCount).toBeGreaterThan(0);
  });

  it('surfaces intentional Context Pack drift as report-only evidence', () => {
    const report = compareJudgmentArtifacts(parseArgs([
      '--baseline',
      'fixtures/variance/run-a.judgment.json',
      '--candidate',
      'fixtures/variance/run-c.context-drift.judgment.json',
    ]));

    expect(report.summary.status).toBe('drift');
    expect(report.normalizedJudgment.match).toBe(false);
    expect(report.findings).toEqual(expect.arrayContaining([
      expect.objectContaining({
        category: 'context-drift',
        sourceInputKind: 'context-pack',
        reportOnly: true,
        affectedEvidencePath: '$.inputFingerprints.contextPack[0].sha256',
      }),
    ]));
  });

  it('writes JSON and Markdown reports from the CLI', () => {
    resetOutputDir();
    const jsonPath = join(outputDir, 'variance-report.json');
    const markdownPath = join(outputDir, 'variance-report.md');

    const result = spawnSync('node', [
      scriptPath,
      '--baseline',
      'fixtures/variance/run-a.judgment.json',
      '--candidate',
      'fixtures/variance/run-c.context-drift.judgment.json',
      '--output-json',
      jsonPath,
      '--output-md',
      markdownPath,
    ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(existsSync(jsonPath)).toBe(true);
    expect(existsSync(markdownPath)).toBe(true);
    const report = JSON.parse(readFileSync(jsonPath, 'utf8'));
    expect(report.contractId).toBe('variance-report.v1');
    expect(readFileSync(markdownPath, 'utf8')).toContain('## Drift findings');
  });

  it('treats -- as the end-of-options marker', () => {
    expect(() => parseArgs([
      '--baseline',
      'fixtures/variance/run-a.judgment.json',
      '--candidate',
      'fixtures/variance/run-b.same-inputs.judgment.json',
      '--',
      '--unknown-after-separator',
    ])).not.toThrow();
  });

  it('prunes volatile-only containers during normalization', () => {
    resetOutputDir();
    const baselinePath = join(outputDir, 'baseline.json');
    const candidatePath = join(outputDir, 'candidate.json');
    writeFileSync(baselinePath, JSON.stringify({
      schemaVersion: 'judgment-artifact-fixture/v1',
      inputFingerprints: {},
      judgmentArtifacts: [
        {
          path: 'artifacts/quality/variance-report.json',
          status: 'report-only',
        },
      ],
    }));
    writeFileSync(candidatePath, JSON.stringify({
      schemaVersion: 'judgment-artifact-fixture/v1',
      metadata: {
        generatedAt: '2026-07-01T00:00:00.000Z',
      },
      inputFingerprints: {},
      judgmentArtifacts: [
        {
          path: 'artifacts/quality/variance-report.json',
          status: 'report-only',
        },
      ],
    }));

    const report = compareJudgmentArtifacts(parseArgs([
      '--baseline',
      baselinePath,
      '--candidate',
      candidatePath,
    ]));
    expect(report.summary.status).toBe('stable');
    expect(report.findings).toHaveLength(0);
    expect(report.expectedDifferences).toEqual(expect.arrayContaining([
      expect.objectContaining({
        affectedEvidencePath: '$.metadata.generatedAt',
        fieldName: 'generatedAt',
      }),
    ]));
  });
});
