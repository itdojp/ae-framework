import { describe, expect, it } from 'vitest';
import {
  collectRequiredLabels,
  getAssuranceEscalationPolicy,
  getGateCheckPatternsForLabel,
  isPlanArtifactRequired,
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

  it('infers high risk when release policy is changed', () => {
    const inferred = inferRiskLevel(policy, ['policy/release-policy.yml']);
    expect(inferred.level).toBe(getRiskLabels(policy).high);
    expect(inferred.highRiskPathMatches).toContain('policy/release-policy.yml');
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

  it('collects trace label requirement for trace validation changes', () => {
    const { requiredLabels } = collectRequiredLabels(policy, ['scripts/trace/render-trace-summary.mjs']);
    expect(requiredLabels).toContain('run-trace');
  });

  it('collects assurance enforcement label for assurance lane changes', () => {
    const { requiredLabels } = collectRequiredLabels(policy, ['scripts/assurance/aggregate-lanes.mjs']);
    expect(requiredLabels).toContain('enforce-assurance');
  });

  it('collects discovery enforcement label for discovery contract changes', () => {
    const { requiredLabels } = collectRequiredLabels(policy, ['scripts/discovery-pack/validate.mjs']);
    expect(requiredLabels).toContain('enforce-discovery');
  });

  it('returns check patterns for label-gated checks', () => {
    const patterns = getGateCheckPatternsForLabel(policy, 'enforce-context-pack');
    expect(patterns).toContain('context-pack-e2e');
  });

  it('returns trace validation check pattern for run-trace', () => {
    const patterns = getGateCheckPatternsForLabel(policy, 'run-trace');
    expect(patterns).toContain('trace-conformance');
    expect(patterns).toContain('KvOnce Trace Validation');
  });

  it('returns verify-lite check pattern for enforce-assurance', () => {
    const patterns = getGateCheckPatternsForLabel(policy, 'enforce-assurance');
    expect(patterns).toContain('verify-lite');
  });

  it('returns verify-lite check pattern for enforce-discovery', () => {
    const patterns = getGateCheckPatternsForLabel(policy, 'enforce-discovery');
    expect(patterns).toContain('verify-lite');
  });

  it('defines assurance escalation lanes for report-only, manual approval, and blocking modes', () => {
    const escalation = getAssuranceEscalationPolicy(policy);

    expect(escalation.defaultMode).toBe('report-only');
    expect(escalation.waiverRequiredFields).toEqual([
      'owner',
      'reason',
      'expires',
      'relatedClaimIds',
      'evidenceRefs',
      'sourceArtifactId',
    ]);
    expect(escalation.lanes).toMatchObject({
      ordinary: { decision: 'report-only' },
      risk_high: { decision: 'manual-approval' },
      enforce_assurance: { decision: 'block' },
      critical_core: { decision: 'manual-approval-or-block' },
    });
    expect(escalation.lanes.risk_high.trigger_labels).toContain('risk:high');
    expect(escalation.lanes.enforce_assurance.trigger_labels).toContain('enforce-assurance');
    expect(escalation.findingClasses).toMatchObject({
      missing_required_lane: {
        ordinary: 'report-only',
        risk_high: 'manual-approval',
        enforce_assurance: 'block',
      },
      waiver_metadata_gap: {
        ordinary: 'report-only',
        risk_high: 'manual-approval',
        enforce_assurance: 'block',
      },
      unresolved_claim: {
        ordinary: 'report-only',
        risk_high: 'manual-approval',
        enforce_assurance: 'block',
      },
    });
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

  it('respects high_risk.require_plan_artifact toggle', () => {
    expect(isPlanArtifactRequired(policy)).toBe(true);
    const relaxedPolicy = {
      ...policy,
      high_risk: {
        ...(policy.high_risk || {}),
        require_plan_artifact: false,
      },
    };
    expect(isPlanArtifactRequired(relaxedPolicy)).toBe(false);
  });
});
