import { describe, expect, it } from 'vitest';
import {
  collectActionableTasksFromReviewThreads,
  deriveBlockedSummary,
  deriveUnblockActions,
  hasLabel,
  parseGateStatus,
} from '../../../scripts/ci/codex-autopilot-lane.mjs';
import { toActorSet } from '../../../scripts/ci/lib/automation-guards.mjs';

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

  it('prefers latest gate run when conclusions are mixed', () => {
    expect(parseGateStatus([
      {
        __typename: 'CheckRun',
        workflowName: 'Copilot Review Gate',
        name: 'gate',
        status: 'COMPLETED',
        conclusion: 'FAILURE',
        completedAt: '2026-02-12T10:00:00Z',
      },
      {
        __typename: 'CheckRun',
        workflowName: 'Copilot Review Gate',
        name: 'gate',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
        completedAt: '2026-02-12T10:05:00Z',
      },
    ])).toBe('success');

    expect(parseGateStatus([
      {
        __typename: 'CheckRun',
        workflowName: 'Copilot Review Gate',
        name: 'gate',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
        completedAt: '2026-02-12T10:00:00Z',
      },
      {
        __typename: 'CheckRun',
        workflowName: 'Copilot Review Gate',
        name: 'gate',
        status: 'COMPLETED',
        conclusion: 'FAILURE',
        completedAt: '2026-02-12T10:05:00Z',
      },
    ])).toBe('failure');
  });

  it('maps status/reason to deterministic unblock actions', () => {
    expect(deriveUnblockActions('skip', 'missing label autopilot:on')).toEqual([
      'Add label `autopilot:on` and rerun `/autopilot run`.',
    ]);
    expect(deriveUnblockActions('skip', 'draft PR')).toEqual([
      'Mark PR as Ready for review, then rerun `/autopilot run`.',
    ]);
    expect(deriveUnblockActions('blocked', 'merge conflict')).toEqual([
      'Rebase/update branch to resolve merge conflicts, then rerun `/autopilot run`.',
    ]);
    expect(deriveUnblockActions('blocked', 'missing policy labels: run-security, enforce-artifacts')).toEqual([
      'Add labels: run-security, enforce-artifacts. Then rerun `/autopilot run`.',
    ]);
    expect(deriveUnblockActions('blocked', 'actionable review tasks pending: 2')).toEqual([
      'Address actionable non-suggestion review comments (or reply why not applicable), then rerun `/autopilot run`.',
    ]);
    expect(deriveUnblockActions('done', 'checks healthy, waiting for required checks/merge queue')).toEqual([
      'No manual fix required. Wait for required checks or merge queue completion.',
    ]);
    expect(deriveUnblockActions('done', 'auto-merge enabled')).toEqual([
      'No action required.',
    ]);
    expect(deriveUnblockActions('done', 'already merged')).toEqual([
      'No action required.',
    ]);
  });

  it('returns fallback unblock action for unknown reason', () => {
    expect(deriveUnblockActions('done', 'queued')).toEqual([
      'No immediate action required. Monitor PR checks until merge completes.',
    ]);
    expect(deriveUnblockActions('blocked', 'some unknown blocker')).toEqual([
      'Resolve: some unknown blocker. Then rerun `/autopilot run`.',
    ]);
    expect(deriveUnblockActions('blocked', '')).toEqual([
      'Inspect required checks and rerun `/autopilot run`.',
    ]);
    expect(deriveUnblockActions('blocked', 'auto-label failed: label write denied')).toEqual([
      'Grant label-write permission (or disable auto-label) and rerun `/autopilot run`.',
    ]);
  });

  it('formats deterministic blocked summary lines', () => {
    expect(deriveBlockedSummary('merge conflict', [
      'Rebase/update branch to resolve merge conflicts, then rerun `/autopilot run`.',
    ])).toEqual({
      blockedLine: 'Blocked: merge conflict',
      unblockLine: 'To unblock: Rebase/update branch to resolve merge conflicts, then rerun `/autopilot run`.',
    });
  });

  it('collects actionable non-suggestion tasks from unresolved AI-review threads', () => {
    const actorSet = toActorSet(['github-copilot[bot]']);
    const tasks = collectActionableTasksFromReviewThreads([
      {
        isResolved: false,
        path: 'src/a.ts',
        comments: {
          nodes: [
            {
              databaseId: 101,
              author: { login: 'github-copilot[bot]' },
              bodyText: 'Please rename this helper for clarity.',
              path: 'src/a.ts',
              line: 12,
              startLine: 12,
              url: 'https://example.invalid/101',
            },
            {
              databaseId: 102,
              author: { login: 'github-copilot[bot]' },
              bodyText: '```suggestion\nconst value = 1;\n```',
              path: 'src/a.ts',
              line: 13,
              startLine: 13,
              url: 'https://example.invalid/102',
            },
          ],
        },
      },
      {
        isResolved: true,
        path: 'src/b.ts',
        comments: {
          nodes: [
            {
              databaseId: 103,
              author: { login: 'github-copilot[bot]' },
              bodyText: 'Please update this.',
              path: 'src/b.ts',
              line: 8,
              startLine: 8,
              url: 'https://example.invalid/103',
            },
          ],
        },
      },
    ], actorSet);

    expect(tasks).toHaveLength(1);
    expect(tasks[0]).toMatchObject({
      commentId: 101,
      path: 'src/a.ts',
      startLine: 12,
      endLine: 12,
    });
  });
});
