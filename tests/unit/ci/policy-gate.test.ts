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
      statusRollup: [checkRun('verify-lite'), checkRun('gate')],
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
      statusRollup: [checkRun('verify-lite'), checkRun('gate')],
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
      statusRollup: [checkRun('verify-lite'), checkRun('gate')],
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
        checkRun('gate'),
        checkRun('Security Scanning'),
        checkRun('testing-ddd'),
      ],
    });
    expect(result.ok).toBe(true);
    expect(result.errors).toHaveLength(0);
  });
});
