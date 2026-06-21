import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, relative, resolve, sep } from 'node:path';
import { randomUUID } from 'node:crypto';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/demo/run-high-risk-escalation-demo.mjs');
const expectedRoot = resolve(repoRoot, 'examples/assurance-control-plane/high-risk-escalation-demo/expected');
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

describe('high-risk escalation assurance demo', () => {
  it('generates fast-lane and strict-lane reviewer surfaces for selected critical claims', () => {
    mkdirSync(resolve(repoRoot, 'artifacts'), { recursive: true });
    const outputRoot = resolve(repoRoot, 'artifacts', `high-risk-escalation-demo-test-${randomUUID()}`);

    try {
      const result = runScript([
        '--output-root', outputRoot,
        '--generated-at', generatedAt,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('High-Risk Escalation Assurance Demo');
      expect(result.stdout).toContain('selected_critical_claims: 2');
      expect(result.stdout).toContain('selected_high_risk_claim_count: 2');
      expect(result.stdout).toContain('producer_missing_evidence_count: 4');
      expect(result.stdout).toContain('manifest_missing_evidence_claims: 2');
      expect(result.stdout).toContain('normal_policy_result: report-only (ok=true)');
      expect(result.stdout).toContain('high_risk_policy_result: block (ok=false)');
      expect(result.stdout).toContain('network: not used');
      expect(result.stdout).toContain('GitHub token: not required');

      const producerPath = join(outputRoot, 'agents/high-risk-escalation-demo/producer-normalization-summary.json');
      const claimManifestPath = join(outputRoot, 'assurance/high-risk-escalation-demo/claim-evidence-manifest.json');
      const assurancePath = join(outputRoot, 'assurance/high-risk-escalation-demo/assurance-summary.json');
      const planArtifactPath = join(outputRoot, 'plan/high-risk-escalation-demo/high-risk-plan-artifact.json');
      const planValidationPath = join(outputRoot, 'plan/high-risk-escalation-demo/plan-artifact-validation.json');
      const normalPolicyPath = join(outputRoot, 'policy/high-risk-escalation-demo/policy-gate-summary.normal.json');
      const highRiskPolicyPath = join(outputRoot, 'policy/high-risk-escalation-demo/policy-gate-summary.high-risk.json');
      const reviewPath = join(outputRoot, 'review/high-risk-escalation-demo/assurance-review.md');
      const highRiskReviewPath = join(outputRoot, 'review/high-risk-escalation-demo/assurance-review.high-risk.md');

      for (const filePath of [
        producerPath,
        claimManifestPath,
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
        rawSignals: 5,
        changedFiles: 3,
        missingEvidence: 4,
        reportOnlyFindings: 6,
      });
      expect(producer.controlPlaneJudgment.emitsDecision).toBe(false);
      expect(stableJson(producer, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'producer-normalization-summary.json'), 'utf8'),
      );
      expect(readFileSync(join(outputRoot, 'agents/high-risk-escalation-demo/producer-normalization-summary.md'), 'utf8')).toBe(
        readFileSync(join(expectedRoot, 'producer-normalization-summary.md'), 'utf8'),
      );

      const claimManifest = readJson(claimManifestPath);
      expect(claimManifest.schemaVersion).toBe('claim-evidence-manifest/v1');
      expect(claimManifest.claims.map((claim: { id: string }) => claim.id)).toEqual([
        'tenant-isolation-enforced-before-account-read',
        'tenant-isolation-waiver-has-reviewable-metadata',
      ]);
      expect(claimManifest.claims[0]).toMatchObject({
        criticality: 'critical',
        status: 'partial',
      });
      expect(claimManifest.claims[0].missingEvidenceRefs.map((entry: { id: string }) => entry.id)).toEqual([
        'missing-cross-tenant-property-evidence',
        'missing-runtime-tenant-isolation-control',
      ]);
      expect(claimManifest.claims[1].waiverRefs[0]).toMatchObject({
        id: 'waiver-tenant-isolation-rollout-window-001',
        status: 'active',
      });
      expect(claimManifest.claims[1].waiverRefs[0].owner).toBeUndefined();
      expect(stableJson(claimManifest, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'claim-evidence-manifest.json'), 'utf8'),
      );

      const assurance = readJson(assurancePath);
      expect(assurance.schemaVersion).toBe('assurance-summary/v1');
      expect(assurance.claims).toHaveLength(2);
      expect(assurance.claims.every((claim: { status: string }) => claim.status === 'warning')).toBe(true);
      expect(assurance.reviewSurface.claimEvidence.missingEvidenceClaims).toHaveLength(2);
      expect(JSON.stringify(assurance)).not.toContain(repoRoot);

      const planArtifact = readJson(planArtifactPath);
      expect(planArtifact.schemaVersion).toBe('plan-artifact/v1');
      expect(planArtifact.source).toMatchObject({ repository: 'itdojp/ae-framework', prNumber: 3512 });
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
        readFileSync(join(outputRoot, 'policy/high-risk-escalation-demo/policy-gate-summary.normal.md'), 'utf8'),
        outputRoot,
      )).toBe(readFileSync(join(expectedRoot, 'policy-gate-summary.normal.md'), 'utf8'));

      const highRiskPolicy = readJson(highRiskPolicyPath);
      expect(highRiskPolicy.evaluation.ok).toBe(false);
      expect(highRiskPolicy.evaluation.assurance).toMatchObject({
        mode: 'strict',
        result: 'block',
      });
      expect(highRiskPolicy.evaluation.errors).toContain('assurance decision is block');
      expect(highRiskPolicy.evaluation.errors.join('\n')).toContain('missing required evidence');
      expect(highRiskPolicy.evaluation.errors.join('\n')).toContain('missing owner');
      expect(highRiskPolicy.evaluation.errors.join('\n')).toContain('missing reason');
      expect(highRiskPolicy.evaluation.errors.join('\n')).toContain('missing expiry');
      expect(JSON.stringify(highRiskPolicy)).not.toContain(repoRoot);
      expect(stableJson(highRiskPolicy, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'policy-gate-summary.high-risk.json'), 'utf8'),
      );
      expect(normalizeOutputRoot(
        readFileSync(join(outputRoot, 'policy/high-risk-escalation-demo/policy-gate-summary.high-risk.md'), 'utf8'),
        outputRoot,
      )).toBe(readFileSync(join(expectedRoot, 'policy-gate-summary.high-risk.md'), 'utf8'));

      const review = readFileSync(reviewPath, 'utf8');
      expect(review).toContain('## Selected critical claims');
      expect(review).toContain('tenant-isolation-enforced-before-account-read');
      expect(review).toContain('property, runtime-control, schema, unit');
      expect(review).toContain('missing-cross-tenant-property-evidence');
      expect(review).toContain('waiver-tenant-isolation-rollout-window-001');
      expect(review).toContain('not provided');
      expect(review).toContain('For ordinary PRs, report-only findings remain reviewer context');
      expect(review).not.toContain(repoRoot);
      expect(normalizeOutputRoot(review, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'assurance-review.md'), 'utf8'),
      );

      const highRiskReview = readFileSync(highRiskReviewPath, 'utf8');
      expect(highRiskReview).toContain('High-Risk Escalation Assurance Demo Review — High-Risk Strict Lane');
      expect(highRiskReview).toContain('risk:high | strict | block | false');
      expect(highRiskReview).toContain('follow policy decision result=`block` mode=`strict`');
      expect(normalizeOutputRoot(highRiskReview, outputRoot)).toBe(
        readFileSync(join(expectedRoot, 'assurance-review.high-risk.md'), 'utf8'),
      );
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('rejects output roots outside the repository', () => {
    const outputRoot = resolve(repoRoot, '..', `high-risk-escalation-demo-outside-${randomUUID()}`);

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
