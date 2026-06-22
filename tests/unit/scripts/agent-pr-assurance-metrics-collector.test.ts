import { describe, expect, it } from 'vitest';
import { chmodSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { randomUUID } from 'node:crypto';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { validateAgenticMetricsSemantics } from '../../../scripts/ci/lib/agentic-metrics-contract.mjs';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/metrics/collect-agent-pr-assurance-metrics.mjs');
const schemaPath = resolve(repoRoot, 'schema/agentic-metrics.schema.json');
const fixturePath = resolve(repoRoot, 'fixtures/metrics/agent-pr-assurance/offline-input.json');
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
        time_to_merge_minutes: 28,
      });
      expect(productMetrics.required_checks.summary).toMatchObject({
        success_count: 3,
        current_required_failure_count: 0,
        stale_or_superseded_failure_count: 1,
      });
      expect(productMetrics.required_checks.required[0]).toMatchObject({
        name: 'gate',
        classification: 'success',
        attempts: 2,
        stale_or_superseded_failure_count: 1,
      });
      expect(payload.agentPrAssurance.reportOnly).toBe(true);
      expect(payload.agentPrAssurance.limitations.join('\n')).toContain('GitHub API was not called');

      const validate = compileSchema();
      expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);
      expect(validateAgenticMetricsSemantics(payload)).toEqual([]);

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toContain('Agent PR Assurance Metrics');
      expect(markdown).toContain('| gate | success | 2 | 1 | SUCCESS |');
      expect(markdown).toContain('Producer output and metrics are review evidence, not approval.');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('uses gh in live mode and marks absent optional evidence as not_collected instead of implying success', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `metrics-collector-live-test-${randomUUID()}`);
    const fakeGh = join(outputRoot, 'fake-gh.mjs');
    const outputJson = join(outputRoot, 'live-agent-pr-assurance-metrics.json');
    const outputMd = join(outputRoot, 'live-agent-pr-assurance-metrics.md');
    mkdirSync(outputRoot, { recursive: true });
    writeFileSync(fakeGh, `#!/usr/bin/env node\nconsole.log(JSON.stringify({\n  number: 99,\n  title: 'live fixture PR',\n  url: 'https://github.com/example/repo/pull/99',\n  state: 'OPEN',\n  createdAt: '2026-06-23T00:00:00Z',\n  mergedAt: null,\n  isDraft: false,\n  reviewDecision: '',\n  mergeStateStatus: 'CLEAN',\n  headRefOid: 'fake-head',\n  statusCheckRollup: [\n    { __typename: 'CheckRun', name: 'gate', workflowName: 'Copilot Review Gate', status: 'COMPLETED', conclusion: 'SUCCESS', startedAt: '2026-06-23T00:01:00Z', completedAt: '2026-06-23T00:02:00Z' },\n    { __typename: 'CheckRun', name: 'policy-gate', workflowName: 'Policy Gate', status: 'COMPLETED', conclusion: 'SUCCESS', startedAt: '2026-06-23T00:02:00Z', completedAt: '2026-06-23T00:03:00Z' },\n    { __typename: 'CheckRun', name: 'verify-lite', workflowName: 'Verify Lite', status: 'COMPLETED', conclusion: 'SUCCESS', startedAt: '2026-06-23T00:03:00Z', completedAt: '2026-06-23T00:04:00Z' }\n  ]\n}));\n`, 'utf8');
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
      expect(productMetrics.time_to_merge_minutes).toBe('not_collected');
      expect(payload.agentPrAssurance.limitations.join('\n')).toContain('review_threads_total is not_collected');
      expect(payload.agentPrAssurance.limitations.join('\n')).toContain('time_to_merge_minutes is not_collected');

      const validate = compileSchema();
      expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });
});
