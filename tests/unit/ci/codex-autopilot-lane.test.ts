import { describe, expect, it } from 'vitest';
import { hasLabel, parseGateStatus } from '../../../scripts/ci/codex-autopilot-lane.mjs';

describe('codex-autopilot-lane helpers', () => {
  it('detects label presence', () => {
    const pr = {
      labels: [{ name: 'autopilot:on' }, { name: 'ci-stability' }],
    };
    expect(hasLabel(pr, 'autopilot:on')).toBe(true);
    expect(hasLabel(pr, 'missing')).toBe(false);
  });

  it('returns gate status from check rollup', () => {
    expect(parseGateStatus([])).toBe('missing');
    expect(parseGateStatus([
      {
        __typename: 'CheckRun',
        workflowName: 'Copilot Review Gate',
        name: 'gate',
        status: 'IN_PROGRESS',
        conclusion: '',
      },
    ])).toBe('pending');
    expect(parseGateStatus([
      {
        __typename: 'CheckRun',
        workflowName: 'Copilot Review Gate',
        name: 'gate',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
      },
    ])).toBe('success');
    expect(parseGateStatus([
      {
        __typename: 'CheckRun',
        workflowName: 'Copilot Review Gate',
        name: 'gate',
        status: 'COMPLETED',
        conclusion: 'FAILURE',
      },
    ])).toBe('failure');
  });
});
