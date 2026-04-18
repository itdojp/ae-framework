import { describe, expect, it } from 'vitest';
import { buildPolicyGateReport, evaluatePolicyGate } from '../../../scripts/ci/policy-gate.mjs';
import { loadRiskPolicy } from '../../../scripts/ci/lib/risk-policy.mjs';

function checkRun(
  name: string,
  conclusion: string = 'SUCCESS',
  overrides: Record<string, unknown> = {},
) {
  return {
    __typename: 'CheckRun',
    name,
    status: 'COMPLETED',
    conclusion,
    ...overrides,
  };
}

function statusContext(
  context: string,
  state: string = 'SUCCESS',
  overrides: Record<string, unknown> = {},
) {
  return {
    __typename: 'StatusContext',
    context,
    state,
    ...overrides,
  };
}

function planArtifactState(overrides: Record<string, unknown> = {}) {
  return {
    path: '/workspace/artifacts/plan/plan-artifact.json',
    schemaPath: '/workspace/schema/plan-artifact.schema.json',
    present: true,
    result: 'pass',
    validationErrors: [],
    warnings: [],
    riskSelected: 'risk:high',
    source: {
      repository: 'itdojp/ae-framework',
      prNumber: 2535,
      baseRef: 'main',
      headRef: 'feat/2535-plan-artifact',
    },
    ...overrides,
  };
}

describe('policy-gate', () => {
  const policy = loadRiskPolicy('policy/risk-policy.yml');

  it('passes for low-risk PR with required checks', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['src/feature/example.ts'],
      reviews: [],
      statusRollup: [checkRun('verify-lite')],
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
  });

  it('prefers the newest same-name required check over an older cancelled run', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['src/feature/example.ts'],
      reviews: [],
      statusRollup: [
        checkRun('verify-lite', 'CANCELLED', {
          workflowName: 'Verify Lite',
          completedAt: '2026-04-14T06:00:00Z',
        }),
        checkRun('verify-lite', 'SUCCESS', {
          workflowName: 'Verify Lite',
          completedAt: '2026-04-14T06:05:00Z',
        }),
      ],
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
    expect(result.requiredCheckResults[0]?.result.status).toBe('success');
    expect(result.requiredCheckResults[0]?.result.matches).toHaveLength(1);
    expect(result.requiredCheckResults[0]?.result.matches[0]?.conclusion).toBe('SUCCESS');
  });

  it('fails when the newest same-name required check failed after an older success', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['src/feature/example.ts'],
      reviews: [],
      statusRollup: [
        checkRun('verify-lite', 'SUCCESS', {
          workflowName: 'Verify Lite',
          completedAt: '2026-04-14T06:00:00Z',
        }),
        checkRun('verify-lite', 'FAILURE', {
          workflowName: 'Verify Lite',
          completedAt: '2026-04-14T06:05:00Z',
        }),
      ],
    });
    expect(result.ok).toBe(false);
    expect(result.errors).toContain('required check failed: verify-lite');
    expect(result.requiredCheckResults[0]?.result.status).toBe('failure');
    expect(result.requiredCheckResults[0]?.result.matches).toHaveLength(1);
    expect(result.requiredCheckResults[0]?.result.matches[0]?.conclusion).toBe('FAILURE');
  });

  it('uses startedAt fallback when the newest same-name required check is pending', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['src/feature/example.ts'],
      reviews: [],
      statusRollup: [
        checkRun('verify-lite', 'SUCCESS', {
          workflowName: 'Verify Lite',
          completedAt: '2026-04-14T06:00:00Z',
        }),
        checkRun('verify-lite', '', {
          workflowName: 'Verify Lite',
          status: 'IN_PROGRESS',
          startedAt: '2026-04-14T06:05:00Z',
        }),
      ],
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
    expect(result.warnings).toContain('required check not ready yet: verify-lite (pending)');
    expect(result.requiredCheckResults[0]?.result.status).toBe('pending');
    expect(result.requiredCheckResults[0]?.result.matches).toHaveLength(1);
    expect(result.requiredCheckResults[0]?.result.matches[0]?.status).toBe('IN_PROGRESS');
  });

  it('treats a timestamp-less newer rerun as the latest pending required check', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['src/feature/example.ts'],
      reviews: [],
      statusRollup: [
        checkRun('verify-lite', 'SUCCESS', {
          workflowName: 'Verify Lite',
          completedAt: '2026-04-14T06:00:00Z',
        }),
        checkRun('verify-lite', '', {
          workflowName: 'Verify Lite',
          status: 'QUEUED',
        }),
      ],
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
    expect(result.warnings).toContain('required check not ready yet: verify-lite (pending)');
    expect(result.requiredCheckResults[0]?.result.status).toBe('pending');
    expect(result.requiredCheckResults[0]?.result.matches).toHaveLength(1);
    expect(result.requiredCheckResults[0]?.result.matches[0]?.status).toBe('QUEUED');
  });

  it('falls back to the later same-name status context when timestamps are unavailable', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['src/feature/example.ts'],
      reviews: [],
      statusRollup: [
        statusContext('verify-lite', 'FAILURE'),
        statusContext('verify-lite', 'SUCCESS'),
      ],
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
    expect(result.requiredCheckResults[0]?.result.status).toBe('success');
    expect(result.requiredCheckResults[0]?.result.matches).toHaveLength(1);
    expect(result.requiredCheckResults[0]?.result.matches[0]?.type).toBe('status-context');
    expect(result.requiredCheckResults[0]?.result.matches[0]?.conclusion).toBe('SUCCESS');
  });

  it('fails when risk label does not match inferred risk', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['package.json'],
      reviews: [],
      statusRollup: [checkRun('verify-lite')],
    });
    expect(result.ok).toBe(false);
    expect(result.errors.some((item) => item.includes('risk label mismatch'))).toBe(true);
  });

  it('fails high-risk PR without approvals and required labels', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['package.json'],
      reviews: [],
      statusRollup: [checkRun('verify-lite')],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(false);
    expect(result.errors.some((item) => item.includes('human approvals are insufficient'))).toBe(true);
    expect(result.errors.some((item) => item.includes('missing required labels'))).toBe(true);
  });

  it('fails high-risk PR when required plan artifact is missing', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'run-security' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['package.json'],
      reviews: [
        {
          id: 99,
          state: 'APPROVED',
          submitted_at: '2026-03-09T00:00:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [
        checkRun('verify-lite'),
        checkRun('Security Scanning'),
      ],
      planArtifact: {
        present: false,
        result: 'missing',
        validationErrors: [],
        warnings: [],
      },
    });
    expect(result.ok).toBe(false);
    expect(result.errors).toContain('missing required plan artifact: artifacts/plan/plan-artifact.json');
  });

  it('fails high-risk PR when required plan artifact validation fails', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'run-security' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['package.json'],
      reviews: [
        {
          id: 101,
          state: 'APPROVED',
          submitted_at: '2026-03-09T00:00:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [
        checkRun('verify-lite'),
        checkRun('Security Scanning'),
      ],
      planArtifact: planArtifactState({
        result: 'fail',
        validationErrors: ['risk.selected must be risk:high'],
      }),
    });
    expect(result.ok).toBe(false);
    expect(result.errors).toContain('plan artifact validation failed: risk.selected must be risk:high');
  });

  it('passes high-risk PR when approvals, labels, and required gates are green', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'run-security' }, { name: 'enforce-testing' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['package.json', 'tests/unit/sample.test.ts'],
      reviews: [
        {
          id: 100,
          state: 'APPROVED',
          submitted_at: '2026-02-26T00:00:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [
        checkRun('verify-lite'),
        checkRun('Security Scanning'),
        checkRun('testing-ddd'),
      ],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
  });

  it('fails high-risk PR when run-trace label is present but trace check was not executed', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'run-trace' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['.github/workflows/spec-generate-model.yml'],
      reviews: [
        {
          id: 201,
          state: 'APPROVED',
          submitted_at: '2026-03-01T00:00:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [checkRun('verify-lite')],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(false);
    expect(result.errors).toContain('required gate check not green for label run-trace (missing)');
  });

  it('passes high-risk PR when run-trace is satisfied by trace-conformance check', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'run-trace' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['.github/workflows/spec-generate-model.yml'],
      reviews: [
        {
          id: 211,
          state: 'APPROVED',
          submitted_at: '2026-03-01T00:05:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [
        checkRun('verify-lite'),
        checkRun('trace-conformance'),
      ],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
  });

  it('prefers the newest same-name gate check over an older cancelled run', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'run-trace' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['.github/workflows/spec-generate-model.yml'],
      reviews: [
        {
          id: 212,
          state: 'APPROVED',
          submitted_at: '2026-03-01T00:06:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [
        checkRun('verify-lite'),
        checkRun('KvOnce Trace Validation', 'CANCELLED', {
          workflowName: 'Spec Validation',
          completedAt: '2026-04-14T06:00:00Z',
        }),
        checkRun('KvOnce Trace Validation', 'SUCCESS', {
          workflowName: 'Spec Validation',
          completedAt: '2026-04-14T06:05:00Z',
        }),
      ],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
    const traceGate = result.gateCheckResults.find((item) => item.label === 'run-trace');
    expect(traceGate?.result.status).toBe('success');
    expect(traceGate?.result.matches).toHaveLength(1);
    expect(traceGate?.result.matches[0]?.conclusion).toBe('SUCCESS');
  });

  it('does not enforce assurance labels on low-risk assurance changes', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['scripts/ci/enforce-assurance-summary.mjs'],
      statusRollup: [checkRun('verify-lite')],
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
    expect(result.missingRequiredLabels).toContain('enforce-assurance');
  });

  it('does not enforce discovery labels on low-risk discovery changes', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['src/cli/discovery-cli.ts'],
      statusRollup: [checkRun('verify-lite')],
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
    expect(result.missingRequiredLabels).toContain('enforce-discovery');
  });

  it('fails high-risk verify-lite workflow changes without enforce-assurance and enforce-discovery', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['.github/workflows/verify-lite.yml'],
      reviews: [
        {
          id: 214,
          state: 'APPROVED',
          submitted_at: '2026-03-09T00:12:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [checkRun('verify-lite')],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(false);
    expect(result.errors.some((item) => item.includes('missing required labels'))).toBe(true);
    expect(result.missingRequiredLabels).toEqual(['enforce-assurance', 'enforce-discovery']);
  });

  it('fails high-risk verify-lite workflow changes when enforce-discovery is missing', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'enforce-assurance' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['.github/workflows/verify-lite.yml'],
      reviews: [
        {
          id: 215,
          state: 'APPROVED',
          submitted_at: '2026-03-09T00:14:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [checkRun('verify-lite')],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(false);
    expect(result.errors).toContain('missing required labels: enforce-discovery');
  });

  it('fails high-risk verify-lite workflow changes when enforce-assurance is missing', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'enforce-discovery' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['.github/workflows/verify-lite.yml'],
      reviews: [
        {
          id: 2151,
          state: 'APPROVED',
          submitted_at: '2026-03-09T00:14:30Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [checkRun('verify-lite')],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(false);
    expect(result.errors).toContain('missing required labels: enforce-assurance');
  });

  it('passes high-risk verify-lite workflow changes when enforce-assurance and enforce-discovery are present', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [
          { name: 'risk:high' },
          { name: 'enforce-assurance' },
          { name: 'enforce-discovery' },
        ],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['.github/workflows/verify-lite.yml'],
      reviews: [
        {
          id: 216,
          state: 'APPROVED',
          submitted_at: '2026-03-09T00:16:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [checkRun('verify-lite')],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
  });

  it('fails high-risk PR when KvOnce trace validation check fails', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'run-trace' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['.github/workflows/spec-generate-model.yml'],
      reviews: [
        {
          id: 202,
          state: 'APPROVED',
          submitted_at: '2026-03-01T00:10:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [
        checkRun('verify-lite'),
        checkRun('KvOnce Trace Validation', 'FAILURE'),
      ],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(false);
    expect(result.errors).toContain('required gate check not green for label run-trace (failure)');
  });

  it('passes high-risk PR without approvals in solo topology', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'run-security' }, { name: 'enforce-testing' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['package.json', 'tests/unit/sample.test.ts'],
      reviews: [],
      statusRollup: [
        checkRun('verify-lite'),
        checkRun('Security Scanning'),
        checkRun('testing-ddd'),
      ],
      reviewTopology: 'solo',
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
    expect(result.effectiveMinApprovals).toBe(0);
  });

  it('fails when approval override requires more approvals', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:high' }, { name: 'run-security' }, { name: 'enforce-testing' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['package.json', 'tests/unit/sample.test.ts'],
      reviews: [
        {
          id: 120,
          state: 'APPROVED',
          submitted_at: '2026-02-26T00:00:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [
        checkRun('verify-lite'),
        checkRun('Security Scanning'),
        checkRun('testing-ddd'),
      ],
      reviewTopology: 'team',
      approvalOverride: '2',
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(false);
    expect(result.errors.some((item) => item.includes('required 2, got 1'))).toBe(true);
    expect(result.effectiveMinApprovals).toBe(2);
  });

  it('falls back with warning when topology or override is invalid', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['src/feature/example.ts'],
      reviews: [],
      statusRollup: [checkRun('verify-lite')],
      reviewTopology: 'unknown',
      approvalOverride: '-1',
    });
    expect(result.ok).toBe(true);
    expect(result.reviewTopology).toBe('team');
    expect(result.warnings.some((item) => item.includes('invalid review topology'))).toBe(true);
    expect(result.warnings.some((item) => item.includes('AE_POLICY_MIN_HUMAN_APPROVALS'))).toBe(true);
  });

  it('does not read process env implicitly for topology decisions', () => {
    const prevTopology = process.env.AE_REVIEW_TOPOLOGY;
    const prevOverride = process.env.AE_POLICY_MIN_HUMAN_APPROVALS;
    process.env.AE_REVIEW_TOPOLOGY = 'solo';
    process.env.AE_POLICY_MIN_HUMAN_APPROVALS = '9';
    try {
      const result = evaluatePolicyGate({
        policy,
        pullRequest: {
          labels: [{ name: 'risk:high' }, { name: 'run-security' }, { name: 'enforce-testing' }],
          body: '## Rollback\nnone\n\n## Acceptance\nok',
        },
        changedFiles: ['package.json', 'tests/unit/sample.test.ts'],
        reviews: [
          {
            id: 130,
            state: 'APPROVED',
            submitted_at: '2026-02-26T00:00:00Z',
            user: { login: 'reviewer1', type: 'User' },
          },
        ],
        statusRollup: [
          checkRun('verify-lite'),
          checkRun('Security Scanning'),
          checkRun('testing-ddd'),
        ],
        planArtifact: planArtifactState(),
      });
      expect(result.reviewTopology).toBe('team');
      expect(result.effectiveMinApprovals).toBe(1);
      expect(result.ok).toBe(true);
    } finally {
      if (prevTopology === undefined) delete process.env.AE_REVIEW_TOPOLOGY;
      else process.env.AE_REVIEW_TOPOLOGY = prevTopology;
      if (prevOverride === undefined) delete process.env.AE_POLICY_MIN_HUMAN_APPROVALS;
      else process.env.AE_POLICY_MIN_HUMAN_APPROVALS = prevOverride;
    }
  });

  it('allows high-risk PR without policy labels when require_policy_labels is false', () => {
    const relaxedPolicy = {
      ...policy,
      high_risk: {
        ...(policy.high_risk || {}),
        require_policy_labels: false,
      },
    };
    const result = evaluatePolicyGate({
      policy: relaxedPolicy,
      pullRequest: {
        labels: [{ name: 'risk:high' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['package.json'],
      reviews: [
        {
          id: 101,
          state: 'APPROVED',
          submitted_at: '2026-02-26T00:10:00Z',
          user: { login: 'reviewer1', type: 'User' },
        },
      ],
      statusRollup: [checkRun('verify-lite')],
      planArtifact: planArtifactState(),
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
    expect(result.warnings.some((item) => item.includes('policy labels missing'))).toBe(true);
  });

  it('warns instead of failing for invalid optional plan artifact on low-risk PR', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## Acceptance\nok',
      },
      changedFiles: ['src/feature/example.ts'],
      reviews: [],
      statusRollup: [checkRun('verify-lite')],
      planArtifact: planArtifactState({
        result: 'fail',
        validationErrors: ['missing rollbackPlan'],
      }),
    });
    expect(result.ok).toBe(true);
    expect(result.warnings.some((item) => item.includes('plan artifact validation failed'))).toBe(true);
  });

  it('treats Japanese acceptance headings as valid template section', () => {
    const result = evaluatePolicyGate({
      policy,
      pullRequest: {
        labels: [{ name: 'risk:low' }],
        body: '## Rollback\nnone\n\n## 受入基準\nok',
      },
      changedFiles: ['src/feature/example.ts'],
      reviews: [],
      statusRollup: [checkRun('verify-lite')],
    });
    expect(result.warnings.some((item) => item.includes('Acceptance section'))).toBe(false);
  });

  it('builds v1 policy-gate summary report envelope', () => {
    const report = buildPolicyGateReport({
      generatedAtUtc: '2026-03-04T00:00:00.000Z',
      repository: 'itdojp/ae-framework',
      prNumber: 2406,
      changedFiles: ['package.json'],
      evaluation: {
        ok: true,
        errors: [],
        warnings: [],
        inferredRisk: { level: 'risk:low' },
        selectedRiskLabel: 'risk:low',
        currentRiskLabels: ['risk:low'],
        reviewTopology: 'team',
        approvals: 0,
        minApprovals: 1,
        policyMinApprovals: 1,
        topologyMinApprovals: 1,
        effectiveMinApprovals: 1,
        minApprovalsSource: 'policy',
        requiredLabels: [],
        missingRequiredLabels: [],
        requiredCheckResults: [],
        gateCheckResults: [],
        planArtifact: {
          path: '/workspace/artifacts/plan/plan-artifact.json',
          schemaPath: '/workspace/schema/plan-artifact.schema.json',
          present: true,
          result: 'pass',
          validationErrors: [],
          warnings: [],
          riskSelected: 'risk:high',
          source: {
            repository: 'itdojp/ae-framework',
            prNumber: 2406,
          },
          required: true,
          errors: [],
        },
      },
    });

    expect(report.schemaVersion).toBe('policy-gate-summary/v1');
    expect(report.contractId).toBe('policy-gate-summary.v1');
    expect(report.prNumber).toBe(2406);
  });
});
