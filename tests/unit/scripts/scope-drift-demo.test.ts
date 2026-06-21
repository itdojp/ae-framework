import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, relative, resolve, sep } from 'node:path';
import { randomUUID } from 'node:crypto';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/demo/run-scope-drift-demo.mjs');
const expectedRoot = resolve(repoRoot, 'examples/assurance-control-plane/scope-drift-demo/expected');
const generatedAt = '2026-06-21T00:00:00.000Z';

const runScript = (args: string[]) => spawnSync('node', [scriptPath, ...args], {
  cwd: repoRoot,
  encoding: 'utf8',
  timeout: 120_000,
});

const readJson = (filePath: string) => JSON.parse(readFileSync(filePath, 'utf8'));
const toPosixPath = (filePath: string) => filePath.split(sep).join('/');
const normalizeOutputRoot = (content: string, outputRoot: string) => {
  const relativeOutputRoot = toPosixPath(relative(repoRoot, outputRoot));
  const absoluteOutputRoot = toPosixPath(outputRoot);
  return content
    .split(absoluteOutputRoot).join('artifacts')
    .split(relativeOutputRoot).join('artifacts');
};
const stableJson = (value: unknown, outputRoot: string) => normalizeOutputRoot(`${JSON.stringify(value, null, 2)}\n`, outputRoot);

describe('scope drift assurance demo', () => {
  it('generates report-only and high-risk reviewer surfaces for scope drift', () => {
    mkdirSync(resolve(repoRoot, 'artifacts'), { recursive: true });
    const outputRoot = resolve(repoRoot, 'artifacts', `scope-drift-demo-test-${randomUUID()}`);

    try {
      const result = runScript([
        '--output-root', outputRoot,
        '--generated-at', generatedAt,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('Scope Drift Assurance Demo');
      expect(result.stdout).toContain('scope_drift_finding_count: 2');
      expect(result.stdout).toContain('normal_policy_result: report-only (ok=true)');
      expect(result.stdout).toContain('high_risk_policy_result: block (ok=false)');
      expect(result.stdout).toContain('network: not used');
      expect(result.stdout).toContain('GitHub token: not required');

      const producerPath = join(outputRoot, 'agents/scope-drift-demo/producer-normalization-summary.json');
      const boundaryPath = join(outputRoot, 'context-pack/scope-drift-demo/boundary-map-summary.json');
      const boundaryReportPath = join(outputRoot, 'context-pack/scope-drift-demo/context-pack-boundary-map-report.json');
      const boundaryReportMdPath = join(outputRoot, 'context-pack/scope-drift-demo/context-pack-boundary-map-report.md');
      const assurancePath = join(outputRoot, 'assurance/scope-drift-demo/assurance-summary.json');
      const planArtifactPath = join(outputRoot, 'plan/scope-drift-demo/high-risk-plan-artifact.json');
      const planValidationPath = join(outputRoot, 'plan/scope-drift-demo/plan-artifact-validation.json');
      const normalPolicyPath = join(outputRoot, 'policy/scope-drift-demo/policy-gate-summary.normal.json');
      const highRiskPolicyPath = join(outputRoot, 'policy/scope-drift-demo/policy-gate-summary.high-risk.json');
      const reviewPath = join(outputRoot, 'review/scope-drift-demo/assurance-review.md');
      const highRiskReviewPath = join(outputRoot, 'review/scope-drift-demo/assurance-review.high-risk.md');

      for (const filePath of [
        producerPath,
        boundaryPath,
        boundaryReportPath,
        boundaryReportMdPath,
        assurancePath,
        planArtifactPath,
        planValidationPath,
        normalPolicyPath,
        highRiskPolicyPath,
        reviewPath,
        highRiskReviewPath,
      ]) {
        expect(existsSync(filePath), `${filePath} should exist`).toBe(true);
      }

      const producer = readJson(producerPath);
      expect(producer.schemaVersion).toBe('producer-normalization-summary/v1');
      expect(producer.summary).toMatchObject({
        changedFiles: 4,
        missingEvidence: 2,
        reportOnlyFindings: 4,
      });
      expect(stableJson(producer, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'producer-normalization-summary.json'), 'utf8'),
      );
      expect(readFileSync(join(outputRoot, 'agents/scope-drift-demo/producer-normalization-summary.md'), 'utf8')).toBe(
        readFileSync(join(expectedRoot, 'producer-normalization-summary.md'), 'utf8'),
      );
      expect(producer.producerAssertions.changedFiles.map((entry: { path: string }) => entry.path)).toContain(
        'src/payments/settlement-retry.ts',
      );
      expect(producer.controlPlaneJudgment.emitsDecision).toBe(false);

      const boundary = readJson(boundaryPath);
      expect(boundary.schemaVersion).toBe('context-pack-boundary-map-summary/v1');
      expect(boundary.status).toBe('drift');
      expect(boundary.counts.totalFindings).toBe(2);
      expect(boundary.reviewEvidence.some((entry: { file: string }) => entry.file === 'src/payments/settlement-retry.ts')).toBe(true);
      expect(stableJson(boundary, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'boundary-map-summary.json'), 'utf8'),
      );

      const boundaryReport = readJson(boundaryReportPath);
      expect(boundaryReport.schemaVersion).toBe('context-pack-boundary-map-report/v1');
      expect(boundaryReport.status).toBe('review');
      expect(boundaryReport.violations).toHaveLength(2);
      expect(stableJson(boundaryReport, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'boundary-map-report.json'), 'utf8'),
      );
      expect(readFileSync(boundaryReportMdPath, 'utf8')).toBe(
        readFileSync(join(expectedRoot, 'boundary-map-report.md'), 'utf8'),
      );

      const assurance = readJson(assurancePath);
      expect(assurance.schemaVersion).toBe('assurance-summary/v1');
      expect(assurance.reviewSurface.boundaryMap.status).toBe('drift');
      expect(assurance.reviewSurface.recommendedReviewerAction.action).toBe('review-boundary-map');
      expect(JSON.stringify(assurance)).not.toContain(repoRoot);

      const planArtifact = readJson(planArtifactPath);
      expect(planArtifact.schemaVersion).toBe('plan-artifact/v1');
      expect(planArtifact.source).toMatchObject({ repository: 'itdojp/ae-framework', prNumber: 3511 });
      expect(stableJson(planArtifact, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'high-risk-plan-artifact.json'), 'utf8'),
      );
      const planValidation = readJson(planValidationPath);
      expect(planValidation.result).toBe('pass');
      expect(JSON.stringify(planValidation)).not.toContain(repoRoot);

      const normalPolicy = readJson(normalPolicyPath);
      expect(normalPolicy.evaluation.ok).toBe(true);
      expect(normalPolicy.evaluation.assurance).toMatchObject({
        mode: 'report-only',
        result: 'report-only',
      });
      expect(JSON.stringify(normalPolicy)).not.toContain(repoRoot);
      expect(stableJson(normalPolicy, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'policy-gate-summary.normal.json'), 'utf8'),
      );
      expect(normalizeOutputRoot(
        readFileSync(join(outputRoot, 'policy/scope-drift-demo/policy-gate-summary.normal.md'), 'utf8'),
        outputRoot,
      )).toBe(readFileSync(join(expectedRoot, 'policy-gate-summary.normal.md'), 'utf8'));

      const highRiskPolicy = readJson(highRiskPolicyPath);
      expect(highRiskPolicy.evaluation.ok).toBe(false);
      expect(highRiskPolicy.evaluation.assurance).toMatchObject({
        mode: 'strict',
        result: 'block',
      });
      expect(highRiskPolicy.evaluation.errors).toContain('assurance decision is block');
      expect(JSON.stringify(highRiskPolicy)).not.toContain(repoRoot);
      expect(stableJson(highRiskPolicy, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'policy-gate-summary.high-risk.json'), 'utf8'),
      );
      expect(normalizeOutputRoot(
        readFileSync(join(outputRoot, 'policy/scope-drift-demo/policy-gate-summary.high-risk.md'), 'utf8'),
        outputRoot,
      )).toBe(readFileSync(join(expectedRoot, 'policy-gate-summary.high-risk.md'), 'utf8'));

      const review = readFileSync(reviewPath, 'utf8');
      expect(review).toContain('## Boundary / scope status');
      expect(review).toContain('src/payments/settlement-retry.ts');
      expect(review).toContain('recommendedReviewerAction: `review-boundary-map`');
      expect(review).toContain('For ordinary PRs, report-only findings remain reviewer context');
      expect(review).not.toContain(repoRoot);
      expect(normalizeOutputRoot(review, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'assurance-review.md'), 'utf8'),
      );

      const highRiskReview = readFileSync(highRiskReviewPath, 'utf8');
      expect(highRiskReview).toContain('Scope Drift Assurance Demo Review — High-Risk Strict Lane');
      expect(highRiskReview).toContain('block');
      expect(normalizeOutputRoot(highRiskReview, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'assurance-review.high-risk.md'), 'utf8'),
      );
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('rejects output roots outside the repository', () => {
    const outputRoot = resolve(repoRoot, '..', `scope-drift-demo-outside-${randomUUID()}`);

    try {
      const result = runScript([
        '--output-root', outputRoot,
        '--generated-at', generatedAt,
      ]);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('output-root must stay under repository root');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });
});
