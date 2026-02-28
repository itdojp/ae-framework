import { describe, expect, it } from 'vitest';
import {
  buildReleasePlan,
  evaluateReleaseVerify,
  parseReleasePolicy,
  type ReleasePolicy,
} from '../../../src/cli/release-cli.js';

const basePolicy: ReleasePolicy = {
  schemaVersion: 'ae-release-policy/v1',
  version: 1,
  updatedAt: '2026-02-28T00:00:00Z',
  owner: 'ae-framework',
  rolloutStrategy: {
    mode: 'canary',
    percentSteps: [1, 5, 25, 100],
    pauseSeconds: 300,
    maxDurationSeconds: 3600,
  },
  healthSignals: {
    errorRate: {
      metricKey: 'errorRate',
      warningThreshold: 0.01,
      criticalThreshold: 0.02,
      comparison: 'lte',
    },
    saturation: {
      metricKey: 'saturation',
      warningThreshold: 0.7,
      criticalThreshold: 0.9,
      comparison: 'lte',
    },
  },
  rollbackPolicy: {
    enabled: true,
    trigger: 'any-critical',
    dryRun: true,
    hook: {
      type: 'command',
      command: 'scripts/ci/automation-rollback.sh',
      timeoutSeconds: 600,
    },
  },
  requiredEvidence: ['postDeployVerify'],
  environments: {
    staging: {
      percentSteps: [10, 50, 100],
      pauseSeconds: 120,
      requiredEvidence: ['qualityGates'],
    },
    production: {
      percentSteps: [1, 5, 25, 100],
      pauseSeconds: 300,
      requiredEvidence: ['qualityGates', 'conformanceSummary'],
    },
  },
};

describe('release cli helpers', () => {
  it('parses release policy object', () => {
    const parsed = parseReleasePolicy(basePolicy);
    expect(parsed.schemaVersion).toBe('ae-release-policy/v1');
    expect(parsed.healthSignals.errorRate.metricKey).toBe('errorRate');
  });

  it('builds release plan using environment-specific rollout', () => {
    const plan = buildReleasePlan(basePolicy, 'staging', 'checkout');
    expect(plan.environment).toBe('staging');
    expect(plan.rollout.percentSteps).toEqual([10, 50, 100]);
    expect(plan.requiredEvidence).toEqual(['postDeployVerify', 'qualityGates']);
    expect(plan.featureName).toBe('checkout');
  });

  it('returns pass when metrics and required evidence are healthy', () => {
    const result = evaluateReleaseVerify(
      basePolicy,
      'production',
      { metrics: { errorRate: 0.005, saturation: 0.5 } },
      { schemaVersion: 'ae-trace-bundle/v1' },
      { status: 'pass' },
      '/tmp/metrics.json',
      '/tmp/trace-bundle.json',
      '/tmp/synthetic.json',
    );

    expect(result.status).toBe('pass');
    expect(result.rollbackRecommended).toBe(false);
    expect(result.summary.failSignals).toBe(0);
    expect(result.summary.missingEvidence).toEqual([]);
  });

  it('returns fail and recommends rollback when critical threshold is violated', () => {
    const result = evaluateReleaseVerify(
      basePolicy,
      'staging',
      { errorRate: 0.04, saturation: 0.4 },
      null,
      null,
      '/tmp/metrics.json',
      null,
      null,
    );

    expect(result.status).toBe('fail');
    expect(result.rollbackRecommended).toBe(true);
    expect(result.summary.failSignals).toBe(1);
  });

  it('returns fail without rollback recommendation when trigger=all-critical and partial fail', () => {
    const policyAllCritical: ReleasePolicy = {
      ...basePolicy,
      rollbackPolicy: {
        ...basePolicy.rollbackPolicy,
        trigger: 'all-critical',
      },
    };
    const result = evaluateReleaseVerify(
      policyAllCritical,
      'staging',
      { errorRate: 0.04, saturation: 0.4 },
      null,
      null,
      '/tmp/metrics.json',
      null,
      null,
    );

    expect(result.status).toBe('fail');
    expect(result.rollbackRecommended).toBe(false);
  });

  it('throws when lte threshold order is invalid', () => {
    const invalidPolicy: ReleasePolicy = {
      ...basePolicy,
      healthSignals: {
        ...basePolicy.healthSignals,
        errorRate: {
          ...basePolicy.healthSignals.errorRate,
          warningThreshold: 0.03,
          criticalThreshold: 0.02,
        },
      },
    };
    expect(() => parseReleasePolicy(invalidPolicy)).toThrow(
      'healthSignals.errorRate has invalid warning/critical threshold order',
    );
  });

  it('throws when rollback trigger value is invalid', () => {
    const invalidPolicy = JSON.parse(JSON.stringify(basePolicy)) as Record<string, unknown>;
    const rollback = invalidPolicy['rollbackPolicy'] as Record<string, unknown>;
    rollback['trigger'] = 'any_critical';
    expect(() => parseReleasePolicy(invalidPolicy)).toThrow(
      'rollbackPolicy.trigger has invalid value: any_critical',
    );
  });

  it('throws when command hook is missing command', () => {
    const invalidPolicy = JSON.parse(JSON.stringify(basePolicy)) as Record<string, unknown>;
    const rollback = invalidPolicy['rollbackPolicy'] as Record<string, unknown>;
    const hook = rollback['hook'] as Record<string, unknown>;
    hook['command'] = '';
    expect(() => parseReleasePolicy(invalidPolicy)).toThrow(
      'rollbackPolicy.hook.command is required when hook.type=command',
    );
  });

  it('returns warn when a metric is missing', () => {
    const result = evaluateReleaseVerify(
      basePolicy,
      'staging',
      { errorRate: 0.005 },
      null,
      { status: 'pass' },
      '/tmp/metrics.json',
      null,
      '/tmp/synthetic.json',
    );

    expect(result.status).toBe('warn');
    expect(result.summary.unknownSignals).toBe(1);
  });
});
