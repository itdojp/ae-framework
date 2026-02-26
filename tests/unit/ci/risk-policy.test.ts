import { describe, expect, it } from 'vitest';
import {
  collectRequiredLabels,
  getGateCheckPatternsForLabel,
  getRiskLabels,
  inferRiskLevel,
  isPolicyLabelRequirementEnabled,
  loadRiskPolicy,
} from '../../../scripts/ci/lib/risk-policy.mjs';

describe('risk-policy', () => {
  const policy = loadRiskPolicy('policy/risk-policy.yml');

  it('infers high risk when workflow files are changed', () => {
    const inferred = inferRiskLevel(policy, ['.github/workflows/ci.yml']);
    expect(inferred.level).toBe(getRiskLabels(policy).high);
    expect(inferred.highRiskPathMatches).toContain('.github/workflows/ci.yml');
  });

  it('infers high risk when dependency manifests are changed', () => {
    const inferred = inferRiskLevel(policy, ['package.json']);
    expect(inferred.level).toBe(getRiskLabels(policy).high);
    expect(inferred.forceHighRiskTriggers.map((item) => item.condition)).toContain(
      'contains_dependency_manifest_change',
    );
  });

  it('collects required labels from changed files', () => {
    const { requiredLabels } = collectRequiredLabels(policy, ['package.json', 'tests/unit/sample.test.ts']);
    expect(requiredLabels).toContain('run-security');
    expect(requiredLabels).toContain('enforce-testing');
  });

  it('returns check patterns for label-gated checks', () => {
    const patterns = getGateCheckPatternsForLabel(policy, 'enforce-context-pack');
    expect(patterns).toContain('context-pack-e2e');
  });

  it('respects high_risk.require_policy_labels toggle', () => {
    expect(isPolicyLabelRequirementEnabled(policy)).toBe(true);
    const relaxedPolicy = {
      ...policy,
      high_risk: {
        ...(policy.high_risk || {}),
        require_policy_labels: false,
      },
    };
    expect(isPolicyLabelRequirementEnabled(relaxedPolicy)).toBe(false);
  });
});
