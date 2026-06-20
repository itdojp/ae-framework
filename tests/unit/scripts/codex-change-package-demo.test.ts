import { mkdirSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { describe, expect, it, onTestFinished } from 'vitest';

const repoRoot = resolve('.');
const normalizerScript = resolve(repoRoot, 'scripts/agents/normalize-producer-output.mjs');
const assuranceScript = resolve(repoRoot, 'scripts/assurance/aggregate-lanes.mjs');
const demoRoot = 'examples/assurance-control-plane/codex-change-package-demo';
const rawFixturePath = `${demoRoot}/producer-output/codex-cli-task-output.json`;
const expectedSummaryJsonPath = `${demoRoot}/expected/producer-normalization-summary.json`;
const expectedSummaryMdPath = `${demoRoot}/expected/producer-normalization-summary.md`;

function createTempDir() {
  const parent = join(repoRoot, '.codex-local', 'tmp');
  mkdirSync(parent, { recursive: true });
  const dir = mkdtempSync(join(parent, 'codex-change-package-demo-'));
  onTestFinished(() => {
    rmSync(dir, { recursive: true, force: true });
  });
  return dir;
}

function runNode(script: string, args: string[]) {
  return spawnSync('node', [script, ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 120_000,
    env: {
      ...process.env,
      NODE_OPTIONS: '',
    },
  });
}

describe('Codex change package assurance demo', () => {
  it('reproduces the expected report-only producer normalization summary', () => {
    const dir = createTempDir();
    const outJson = join(dir, 'producer-normalization-summary.json');
    const outMd = join(dir, 'producer-normalization-summary.md');

    const result = runNode(normalizerScript, [
      '--input', rawFixturePath,
      '--out-json', outJson,
      '--out-md', outMd,
      '--generated-at', '2026-06-20T00:00:00.000Z',
    ]);

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(JSON.parse(readFileSync(outJson, 'utf8'))).toEqual(
      JSON.parse(readFileSync(expectedSummaryJsonPath, 'utf8')),
    );
    expect(readFileSync(outMd, 'utf8')).toBe(readFileSync(expectedSummaryMdPath, 'utf8'));
  });

  it('feeds the normalized producer output into the assurance review surface without emitting a judgment', () => {
    const dir = createTempDir();
    const assuranceJson = join(dir, 'assurance-summary.json');
    const assuranceMd = join(dir, 'assurance-summary.md');

    const result = runNode(assuranceScript, [
      '--assurance-profile', 'fixtures/assurance/sample.assurance-profile.json',
      '--producer-summary', expectedSummaryJsonPath,
      '--output-json', assuranceJson,
      '--output-md', assuranceMd,
    ]);

    expect(result.status, result.stderr || result.stdout).toBe(0);
    const summary = JSON.parse(readFileSync(assuranceJson, 'utf8'));
    expect(summary.reviewSurface.producerSignals).toMatchObject({
      status: 'report-only-findings',
      producerAssertions: 7,
      missingEvidence: 2,
      reportOnlyFindings: 5,
      controlPlaneJudgment: {
        emittedDecisionCount: 0,
        expected: 'producer-output-is-not-control-plane-judgment',
      },
    });
    expect(summary.reviewSurface.producerSignals.producers).toEqual([
      expect.objectContaining({ id: 'codex-cli', category: 'local-agent' }),
    ]);
    expect(summary.reviewSurface.residualRisks).toEqual(expect.arrayContaining([
      expect.objectContaining({
        kind: 'producer-report-only-finding',
        source: 'producer-summary',
      }),
    ]));
    const markdown = readFileSync(assuranceMd, 'utf8');
    expect(markdown).toContain('## Reviewer decision surface');
    expect(markdown).toContain('producerSignals: report-only-findings (reportOnlyFindings=5, missingEvidence=2)');
    expect(markdown).toContain('Producer assertions remain producer assertions');
  });
});
