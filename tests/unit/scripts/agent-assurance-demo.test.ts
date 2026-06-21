import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, relative, resolve, sep } from 'node:path';
import { randomUUID } from 'node:crypto';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/demo/run-agent-assurance-demo.mjs');
const rendererPath = resolve(repoRoot, 'scripts/assurance/render-pr-review-surface.mjs');
const expectedReviewPath = resolve(
  repoRoot,
  'examples/assurance-control-plane/agent-assurance-demo/expected/assurance-review.md',
);
const generatedAt = '2026-06-21T00:00:00.000Z';

const runScript = (args: string[]) => spawnSync('node', [scriptPath, ...args], {
  cwd: repoRoot,
  encoding: 'utf8',
  timeout: 120_000,
});

const readJson = (filePath: string) => JSON.parse(readFileSync(filePath, 'utf8'));
const toPosixPath = (filePath: string) => filePath.split(sep).join('/');
const normalizeOutputRoot = (markdown: string, outputRoot: string) => {
  const relativeOutputRoot = toPosixPath(relative(repoRoot, outputRoot));
  return markdown.split(relativeOutputRoot).join('artifacts');
};

describe('BYO-agent assurance demo', () => {
  it('generates the offline reviewer-surface artifact set', () => {
    mkdirSync(resolve(repoRoot, 'artifacts'), { recursive: true });
    const outputRoot = resolve(repoRoot, 'artifacts', `agent-assurance-demo-test-${randomUUID()}`);

    try {
      const result = runScript([
        '--output-root', outputRoot,
        '--generated-at', generatedAt,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('BYO-Agent Assurance Demo');
      expect(result.stdout).toContain('missing_evidence_finding_count: 2');
      expect(result.stdout).toContain('network: not used');
      expect(result.stdout).toContain('GitHub token: not required');

      const verifyLitePath = join(outputRoot, 'verify-lite/agent-assurance-demo/verify-lite-run-summary.json');
      const producerPath = join(outputRoot, 'agents/agent-assurance-demo/producer-normalization-summary.json');
      const assurancePath = join(outputRoot, 'assurance/agent-assurance-demo/assurance-summary.json');
      const policyPath = join(outputRoot, 'policy/agent-assurance-demo/policy-gate-summary.json');
      const reviewPath = join(outputRoot, 'review/agent-assurance-demo/assurance-review.md');

      for (const filePath of [verifyLitePath, producerPath, assurancePath, policyPath, reviewPath]) {
        expect(existsSync(filePath), `${filePath} should exist`).toBe(true);
      }

      const verifyLite = readJson(verifyLitePath);
      expect(verifyLite.schemaVersion).toBe('1.0.0');
      expect(verifyLite.metadata.runner.name).toBe('agent-assurance-demo-fixture');

      const producer = readJson(producerPath);
      expect(producer.schemaVersion).toBe('producer-normalization-summary/v1');
      expect(producer.summary).toMatchObject({
        missingEvidence: 2,
        reportOnlyFindings: 5,
      });

      const assurance = readJson(assurancePath);
      expect(assurance.schemaVersion).toBe('assurance-summary/v1');
      expect(assurance.reviewSurface.producerSignals.status).toBe('report-only-findings');
      expect(assurance.generatedAt).toBe(generatedAt);
      expect(assurance.metadata.generatedAtUtc).toBe(generatedAt);

      const policy = readJson(policyPath);
      expect(policy.schemaVersion).toBe('policy-gate-summary/v1');
      expect(policy.evaluation.ok).toBe(true);
      expect(policy.evaluation.assurance).toMatchObject({
        mode: 'report-only',
        result: 'report-only',
      });
      expect(policy.evaluation.assurance.agentAssuranceFindings.count).toBeGreaterThanOrEqual(5);
      expect(JSON.stringify(policy)).not.toContain(repoRoot);

      const review = readFileSync(reviewPath, 'utf8');
      expect(review).toContain('## Producer / task scope');
      expect(review).toContain('## Claims and evidence status');
      expect(review).toContain('## Reviewer action list');
      expect(review).toContain('Producer output is displayed as report-only input. It is never rendered as approval.');
      expect(review).toContain('missing |');
      expect(review).toContain('not provided');
      expect(review).not.toContain(repoRoot);
      expect(normalizeOutputRoot(review, outputRoot)).toBe(readFileSync(expectedReviewPath, 'utf8'));
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('renders missing optional artifacts explicitly instead of implying success', () => {
    mkdirSync(resolve(repoRoot, 'artifacts'), { recursive: true });
    const outputRoot = resolve(repoRoot, 'artifacts', `agent-assurance-review-missing-${randomUUID()}`);
    const outputMd = join(outputRoot, 'assurance-review.md');

    try {
      const result = spawnSync('node', [
        rendererPath,
        '--generated-at', generatedAt,
        '--output-md', outputMd,
      ], {
        cwd: repoRoot,
        encoding: 'utf8',
        timeout: 120_000,
      });

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const review = readFileSync(outputMd, 'utf8');
      expect(review).toContain('| producer-normalization-summary | artifacts/agents/producer-normalization-summary.json | missing |');
      expect(review).toContain('| policy-gate-summary | artifacts/ci/policy-gate-summary.json | missing |');
      expect(review).toContain('| boundary-map-summary | artifacts/context-pack/boundary-map-summary.json | missing |');
      expect(review).toContain('recommendedReviewerAction: `not provided`');
      expect(review).toContain('Boundary artifact is missing or not provided');
      expect(review).toContain('Claim evidence manifest is missing or not provided');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('rejects output roots outside the repository', () => {
    const outputRoot = resolve(repoRoot, '..', `agent-assurance-demo-outside-${randomUUID()}`);

    try {
      const result = runScript([
        '--output-root', outputRoot,
        '--generated-at', generatedAt,
      ]);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('output-root must stay under the repository root');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });
});
