import { describe, expect, it } from 'vitest';
import { chmodSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { randomUUID } from 'node:crypto';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { validateAgenticMetricsSemantics } from '../../../scripts/ci/lib/agentic-metrics-contract.mjs';
import { collectRequiredCheckClassifications } from '../../../scripts/ci/lib/check-classification.mjs';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/metrics/collect-agent-pr-assurance-metrics.mjs');
const schemaPath = resolve(repoRoot, 'schema/agentic-metrics.schema.json');
const fixturePath = resolve(repoRoot, 'fixtures/metrics/agent-pr-assurance/offline-input.json');
const checkClassificationFixturePath = resolve(repoRoot, 'fixtures/metrics/check-classification/required-check-rollup.json');
const generatedAt = '2026-06-23T00:00:00.000Z';

const runScript = (args: string[]) => spawnSync('node', [scriptPath, ...args], {
  cwd: repoRoot,
  encoding: 'utf8',
  timeout: 120_000,
});

const readJson = (filePath: string) => JSON.parse(readFileSync(filePath, 'utf8'));

function compileSchema() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const schema = readJson(schemaPath);
  return ajv.compile(schema);
}

describe('agent PR assurance metrics collector', () => {
  it('generates reproducible offline JSON and Markdown without treating stale cancelled checks as current failures', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `metrics-collector-test-${randomUUID()}`);
    const outputJson = join(outputRoot, 'agent-pr-assurance-metrics.json');
    const outputMd = join(outputRoot, 'agent-pr-assurance-metrics.md');

    try {
      const result = runScript([
        '--fixture', fixturePath,
        '--generated-at', generatedAt,
        '--output-json', outputJson,
        '--output-md', outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(existsSync(outputJson)).toBe(true);
      expect(existsSync(outputMd)).toBe(true);

      const payload = readJson(outputJson);
      const productMetrics = payload.agentPrAssurance.productMetrics;
      expect(productMetrics).toMatchObject({
        review_threads_total: 4,
        review_threads_unresolved_final: 0,
        scope_drift_finding_count: 2,
        missing_evidence_finding_count: 4,
        selected_high_risk_claim_count: 2,
        ci_rerun_count: 1,
        time_to_merge_minutes: 24,
      });
      expect(productMetrics.required_checks.summary).toMatchObject({
        success_count: 3,
        current_required_failure_count: 0,
        policy_semantic_failure_count: 0,
        manual_rerun_required_count: 0,
        stale_or_superseded_failure_count: 1,
        stale_cancelled_count: 1,
        same_head_stale_count: 1,
        semantic_blocking_failure_count: 0,
        operational_note_count: 1,
      });
      expect(productMetrics.ci_rerun_classification_counts).toEqual({
        total: 1,
        stale_cancelled: 1,
        superseded: 0,
        same_head_stale: 1,
        manual_rerun_required: 0,
      });
      expect(productMetrics.required_checks.required[0]).toMatchObject({
        name: 'gate',
        classification: 'success',
        review_disposition: 'operational_note',
        attempts: 2,
        stale_or_superseded_failure_count: 1,
        stale_cancelled_count: 1,
        same_head_stale_count: 1,
        stale_attempts: [
          expect.objectContaining({ classification: 'stale_cancelled', sameHeadStale: true }),
        ],
      });
      expect(payload.agentPrAssurance.metrics.agent_regression_signal).toMatchObject({
        currentFailures: 0,
        staleOrSupersededFailures: 1,
        operationalNotes: 1,
        classificationSource: 'statusCheckRollup',
        regressed: false,
      });
      expect(payload.agentPrAssurance.reportOnly).toBe(true);
      expect(payload.agentPrAssurance.limitations.join('\n')).toContain('GitHub API was not called');

      const validate = compileSchema();
      expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);
      expect(validateAgenticMetricsSemantics(payload)).toEqual([]);

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toContain('Agent PR Assurance Metrics');
      expect(markdown).toContain('### Operational notes');
      expect(markdown).toContain('### Non-blocking checks');
      expect(markdown).toContain('| gate | success | operational_note | 2 | 1 | 0 | 1 | SUCCESS |');
      expect(markdown).toContain('ci_rerun_classification_counts');
      expect(markdown).toContain('Producer output and metrics are review evidence, not approval.');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });


  it('classifies stale, cancelled, superseded, policy, and manual-rerun check states separately', () => {
    const fixture = readJson(checkClassificationFixturePath);
    const requiredChecks = collectRequiredCheckClassifications(
      fixture.statusCheckRollup,
      fixture.requiredChecks,
      { pullRequestHeadSha: fixture.pullRequestHeadSha },
    );

    expect(requiredChecks.summary).toMatchObject({
      required_count: 5,
      collected_count: 5,
      success_count: 2,
      pending_count: 1,
      current_required_failure_count: 0,
      policy_semantic_failure_count: 1,
      manual_rerun_required_count: 1,
      stale_or_superseded_failure_count: 2,
      stale_cancelled_count: 1,
      superseded_count: 1,
      same_head_stale_count: 1,
      semantic_blocking_failure_count: 1,
      operational_note_count: 3,
    });
    expect(requiredChecks.required.find((entry) => entry.name === 'gate')).toMatchObject({
      classification: 'success',
      review_disposition: 'operational_note',
      stale_attempts: [expect.objectContaining({ classification: 'stale_cancelled', sameHeadStale: true })],
    });
    expect(requiredChecks.required.find((entry) => entry.name === 'verify-lite')).toMatchObject({
      classification: 'success',
      stale_attempts: [expect.objectContaining({ classification: 'superseded', sameHeadStale: false })],
    });
    expect(requiredChecks.required.find((entry) => entry.name === 'policy-gate')).toMatchObject({
      classification: 'policy_semantic_failure',
      review_disposition: 'blocking',
    });
    expect(requiredChecks.required.find((entry) => entry.name === 'lint')).toMatchObject({
      classification: 'manual_rerun_required',
      review_disposition: 'operational_note',
    });
    expect(requiredChecks.required.find((entry) => entry.name === 'coverage')).toMatchObject({
      classification: 'pending',
      review_disposition: 'pending',
    });

    const statusContextChecks = collectRequiredCheckClassifications([
      {
        __typename: 'StatusContext',
        context: 'legacy-required',
        state: 'SUCCESS',
        targetUrl: 'https://github.com/example/repo/actions/runs/legacy',
      },
    ], ['legacy-required']);
    expect(statusContextChecks.required[0]).toMatchObject({
      name: 'legacy-required',
      classification: 'success',
      latest: {
        conclusion: 'SUCCESS',
        detailsUrl: 'https://github.com/example/repo/actions/runs/legacy',
      },
    });
  });

  it('uses gh in live mode and marks absent optional evidence as not_collected instead of implying success', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `metrics-collector-live-test-${randomUUID()}`);
    const fakeGh = join(outputRoot, 'fake-gh.mjs');
    const outputJson = join(outputRoot, 'live-agent-pr-assurance-metrics.json');
    const outputMd = join(outputRoot, 'live-agent-pr-assurance-metrics.md');
    mkdirSync(outputRoot, { recursive: true });
    writeFileSync(fakeGh, `#!/usr/bin/env node\nconsole.log(JSON.stringify({\n  number: 99,\n  title: 'live fixture PR',\n  url: 'https://github.com/example/repo/pull/99',\n  state: 'OPEN',\n  createdAt: '2026-06-23T00:00:00Z',\n  mergedAt: '2026-06-23T00:10:00Z',\n  isDraft: false,\n  reviewDecision: '',\n  mergeStateStatus: 'CLEAN',\n  headRefOid: 'fake-head',\n  statusCheckRollup: [\n    { __typename: 'CheckRun', name: 'gate', workflowName: 'Copilot Review Gate', status: 'COMPLETED', conclusion: 'SUCCESS', startedAt: '2026-06-23T00:01:00Z', completedAt: '2026-06-23T00:02:00Z' },\n    { __typename: 'CheckRun', name: 'policy-gate', workflowName: 'Policy Gate', status: 'COMPLETED', conclusion: 'SUCCESS', startedAt: '2026-06-23T00:02:00Z', completedAt: '2026-06-23T00:03:00Z' },\n    { __typename: 'CheckRun', name: 'verify-lite', workflowName: 'Verify Lite', status: 'COMPLETED', conclusion: 'SUCCESS', startedAt: '2026-06-23T00:03:00Z', completedAt: '2026-06-23T00:04:00Z' }\n  ]\n}));\n`, 'utf8');
    chmodSync(fakeGh, 0o755);

    try {
      const result = runScript([
        '--repo', 'example/repo',
        '--pr', '99',
        '--gh-bin', fakeGh,
        '--generated-at', generatedAt,
        '--output-json', outputJson,
        '--output-md', outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const payload = readJson(outputJson);
      const productMetrics = payload.agentPrAssurance.productMetrics;
      expect(payload.agentPrAssurance.source).toBe('gh-pr-view');
      expect(productMetrics.required_checks.summary.success_count).toBe(3);
      expect(productMetrics.review_threads_total).toBe('not_collected');
      expect(productMetrics.scope_drift_finding_count).toBe('not_collected');
      expect(payload.agentPrAssurance.metrics.unresolved_claim_count.count).toBe('not_collected');
      expect(productMetrics.time_to_merge_minutes).toBe('not_collected');
      expect(payload.agentPrAssurance.limitations.join('\n')).toContain('review_threads_total is not_collected');
      expect(payload.agentPrAssurance.limitations.join('\n')).toContain('time_to_merge_minutes is not_collected');

      const validate = compileSchema();
      expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('keeps absent statusCheckRollup as not_collected rather than zero-count success', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `metrics-collector-not-collected-test-${randomUUID()}`);
    const fixture = join(outputRoot, 'pr-without-check-rollup.json');
    const outputJson = join(outputRoot, 'not-collected-agent-pr-assurance-metrics.json');
    const outputMd = join(outputRoot, 'not-collected-agent-pr-assurance-metrics.md');
    mkdirSync(outputRoot, { recursive: true });
    writeFileSync(fixture, JSON.stringify({
      repository: 'itdojp/ae-framework',
      prNumber: 3529,
      pullRequest: {
        repository: 'itdojp/ae-framework',
        number: 3529,
        title: 'classify required check states',
        url: 'https://github.com/itdojp/ae-framework/pull/3529',
        state: 'OPEN',
        createdAt: '2026-06-23T00:00:00Z',
        reviewReadyAt: '2026-06-23T00:01:00Z',
        mergedAt: '2026-06-23T00:12:00Z',
        headRefOid: 'fixture-head-without-rollup',
        mergeStateStatus: 'UNKNOWN',
      },
    }, null, 2), 'utf8');

    try {
      const result = runScript([
        '--fixture', fixture,
        '--generated-at', generatedAt,
        '--output-json', outputJson,
        '--output-md', outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const payload = readJson(outputJson);
      const productMetrics = payload.agentPrAssurance.productMetrics;
      expect(productMetrics.required_checks.source).toBe('not_collected');
      expect(productMetrics.required_checks.summary).toMatchObject({
        required_count: 3,
        collected_count: 0,
        success_count: 'not_collected',
        current_required_failure_count: 'not_collected',
        semantic_blocking_failure_count: 'not_collected',
        operational_note_count: 'not_collected',
      });
      expect(productMetrics.ci_rerun_count).toBe('not_collected');
      expect(productMetrics.ci_rerun_classification_counts).toBe('not_collected');
      expect(productMetrics.required_checks.required[0]).toMatchObject({
        name: 'gate',
        collected: false,
        classification: 'not_collected',
        review_disposition: 'not_collected',
      });
      expect(payload.agentPrAssurance.metrics.agent_regression_signal).toMatchObject({
        currentFailures: 'not_collected',
        staleOrSupersededFailures: 'not_collected',
        operationalNotes: 'not_collected',
        classificationSource: 'not_collected',
        regressed: false,
      });
      expect(payload.agentPrAssurance.summary).toContain('required check semantic failures not_collected');
      expect(payload.agentPrAssurance.summary).toContain('operational notes not_collected');

      const validate = compileSchema();
      expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);
      expect(validateAgenticMetricsSemantics(payload)).toEqual([]);

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toContain('### Not collected checks');
      expect(markdown).toContain('| gate | not_collected | not_collected | 0 | 0 | 0 | 0 | not_collected |');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });
});
