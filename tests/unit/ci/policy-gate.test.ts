import { describe, expect, it } from 'vitest';
import { evaluatePolicyGate } from '../../../scripts/ci/policy-gate.mjs';
import { loadRiskPolicy } from '../../../scripts/ci/lib/risk-policy.mjs';

function checkRun(name: string, conclusion: string = 'SUCCESS') {
  return {
    __typename: 'CheckRun',
    name,
    status: 'COMPLETED',
    conclusion,
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
    });
    expect(result.ok).toBe(false);
    expect(result.errors.some((item) => item.includes('human approvals are insufficient'))).toBe(true);
    expect(result.errors.some((item) => item.includes('missing required labels'))).toBe(true);
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
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
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
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
    expect(result.warnings.some((item) => item.includes('policy labels missing'))).toBe(true);
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
});
