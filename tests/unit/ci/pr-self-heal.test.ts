import { describe, expect, it } from 'vitest';
import {
  parseRunId,
  summarizeCheckRollup,
  classifyPr,
  planActions,
} from '../../../scripts/ci/pr-self-heal.mjs';

describe('pr-self-heal helpers', () => {
  it('extracts run id from GitHub actions details URL', () => {
    expect(parseRunId('https://github.com/a/b/actions/runs/123456789/job/1')).toBe(123456789);
    expect(parseRunId('https://example.invalid/no-run-id')).toBeNull();
  });

  it('collects rerunnable failed runs and mixed checks', () => {
    const now = Date.UTC(2026, 1, 12, 10, 0, 0);
    const rollup = [
      {
        __typename: 'CheckRun',
        workflowName: 'Copilot Review Gate',
        name: 'gate',
        status: 'COMPLETED',
        conclusion: 'FAILURE',
        detailsUrl: 'https://github.com/a/b/actions/runs/100/job/1',
        completedAt: new Date(now - 60_000).toISOString(),
      },
      {
        __typename: 'CheckRun',
        workflowName: 'Copilot Review Gate',
        name: 'gate',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
        detailsUrl: 'https://github.com/a/b/actions/runs/101/job/1',
        completedAt: new Date(now - 30_000).toISOString(),
      },
      {
        __typename: 'CheckRun',
        workflowName: 'Verify Lite',
        name: 'verify-lite',
        status: 'IN_PROGRESS',
        conclusion: '',
        detailsUrl: 'https://github.com/a/b/actions/runs/102/job/1',
        completedAt: '',
      },
    ];

    const summary = summarizeCheckRollup(rollup, {
      nowMs: now,
      maxAgeMs: 10 * 60 * 1000,
      rerunBlacklist: new Set(),
    });

    expect(summary.counts.failure).toBe(1);
    expect(summary.counts.pending).toBe(1);
    expect(summary.rerunnableRunIds).toContain(100);
    expect(summary.mixedKeys.length).toBe(1);
  });

  it('classifies actionable PR with behind + failed checks', () => {
    const state = classifyPr(
      {
        number: 1,
        title: 'test',
        url: 'https://example.invalid/pr/1',
        isDraft: false,
        mergeable: 'MERGEABLE',
        mergeStateStatus: 'BEHIND',
        statusCheckRollup: [
          {
            __typename: 'CheckRun',
            workflowName: 'Copilot Review Gate',
            name: 'gate',
            status: 'COMPLETED',
            conclusion: 'FAILURE',
            detailsUrl: 'https://github.com/a/b/actions/runs/222/job/1',
            completedAt: new Date().toISOString(),
          },
        ],
      },
      {
        nowMs: Date.now(),
        maxAgeMinutes: 60,
        rerunBlacklist: new Set(),
      },
    );

    expect(state.isBehind).toBe(true);
    expect(state.hasConflict).toBe(false);

    const plan = planActions(state);
    expect(plan.status).toBe('actionable');
    expect(plan.actions.some((action) => action.type === 'update-branch')).toBe(true);
    expect(plan.actions.some((action) => action.type === 'rerun-failed')).toBe(true);
  });

  it('classifies conflicting PR as blocked', () => {
    const state = classifyPr(
      {
        number: 2,
        title: 'conflict',
        url: 'https://example.invalid/pr/2',
        isDraft: false,
        mergeable: 'CONFLICTING',
        mergeStateStatus: 'DIRTY',
        statusCheckRollup: [],
      },
      {
        nowMs: Date.now(),
        maxAgeMinutes: 60,
        rerunBlacklist: new Set(),
      },
    );

    const plan = planActions(state);
    expect(plan.status).toBe('blocked');
    expect(plan.reason).toContain('conflict');
  });
});
