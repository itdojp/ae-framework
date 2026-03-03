import { describe, expect, it } from 'vitest';
import {
  collectActionableTasksFromReviewThreads,
  createEmptyActionableExecution,
  deriveBlockedSummary,
  deriveUnblockActions,
  formatActionableExecutionLine,
  hasLabel,
  paginateGraphqlConnection,
  parseGateStatus,
  summarizeActionableExecutionResults,
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
    expect(deriveUnblockActions('blocked', 'actionable execution failed: 1/2 failed')).toEqual([
      'Inspect actionable execution results, apply fixes (or adjust `AE_AUTOPILOT_ACTIONABLE_COMMAND`), then rerun `/autopilot run`.',
    ]);
    expect(deriveUnblockActions('blocked', 'actionable execution incomplete: 1/2 skipped')).toEqual([
      'Resolve skipped actionable tasks manually (or update `AE_AUTOPILOT_ACTIONABLE_COMMAND`), then rerun `/autopilot run`.',
    ]);
    expect(deriveUnblockActions('blocked', 'actionable review task scan truncated (pagination required)')).toEqual([
      'Reduce unresolved AI-review threads/comments (or implement pagination support), then rerun `/autopilot run`.',
    ]);
    expect(deriveUnblockActions('blocked', 'max rounds reached without convergence')).toEqual([
      'Wait for in-flight checks/dispatch jobs to settle, then rerun `/autopilot run`.',
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

  it('formats actionable execution summary in deterministic order', () => {
    expect(formatActionableExecutionLine(createEmptyActionableExecution())).toBe(
      'skipped (attempted=0, succeeded=0, failed=0, skipped=0)',
    );
    expect(formatActionableExecutionLine({
      status: 'failed',
      attempted: 3,
      succeeded: 1,
      failed: 1,
      skipped: 1,
    })).toBe('failed (attempted=3, succeeded=1, failed=1, skipped=1)');
  });

  it('summarizes actionable execution preview deterministically', () => {
    expect(summarizeActionableExecutionResults({
      results: [
        { commentId: 303, status: 'failed', reason: 'missing result' },
        { commentId: 101, status: 'success', reason: '' },
        { commentId: 202, status: 'skipped', reason: 'not applicable' },
      ],
    }, 2)).toEqual([
      '1. comment=101 status=success',
      '2. comment=202 status=skipped reason=not applicable',
    ]);
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
              createdAt: '2026-03-02T01:00:00Z',
            },
            {
              databaseId: 102,
              author: { login: 'github-copilot[bot]' },
              bodyText: '```suggestion\nconst value = 1;\n```',
              path: 'src/a.ts',
              line: 13,
              startLine: 13,
              url: 'https://example.invalid/102',
              createdAt: '2026-03-02T01:01:00Z',
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

  it('skips actionable task when a human disposition reply exists in the same thread', () => {
    const actorSet = toActorSet(['github-copilot[bot]']);
    const tasks = collectActionableTasksFromReviewThreads([
      {
        isResolved: false,
        path: 'src/a.ts',
        comments: {
          nodes: [
            {
              databaseId: 201,
              author: { login: 'github-copilot[bot]', __typename: 'Bot' },
              bodyText: 'Please update this branch.',
              path: 'src/a.ts',
              line: 8,
              startLine: 8,
              url: 'https://example.invalid/201',
              createdAt: '2026-03-02T01:00:00Z',
            },
            {
              databaseId: 202,
              author: { login: 'devuser', __typename: 'User' },
              bodyText: 'この指摘は別PRで対応済みのため、ここでは適用しません。',
              path: 'src/a.ts',
              line: 8,
              startLine: 8,
              url: 'https://example.invalid/202',
              createdAt: '2026-03-02T01:01:00Z',
            },
          ],
        },
      },
    ], actorSet);
    expect(tasks).toHaveLength(0);
  });

  it('paginates GraphQL connections when cursors are available', () => {
    const fetchNext = (cursor: string) => {
      if (cursor === 'cursor-1') {
        return {
          pageInfo: { hasNextPage: true, endCursor: 'cursor-2' },
          nodes: [{ id: 2 }],
        };
      }
      if (cursor === 'cursor-2') {
        return {
          pageInfo: { hasNextPage: false, endCursor: null },
          nodes: [{ id: 3 }],
        };
      }
      throw new Error(`unexpected cursor: ${cursor}`);
    };

    expect(paginateGraphqlConnection({
      pageInfo: { hasNextPage: true, endCursor: 'cursor-1' },
      nodes: [{ id: 1 }],
    }, fetchNext)).toEqual({
      nodes: [{ id: 1 }, { id: 2 }, { id: 3 }],
      truncated: false,
    });
  });

  it('keeps fail-closed behavior only when connection pagination cannot continue', () => {
    expect(paginateGraphqlConnection({
      pageInfo: { hasNextPage: true, endCursor: '' },
      nodes: [{ id: 1 }],
    }, () => ({
      pageInfo: { hasNextPage: false, endCursor: null },
      nodes: [{ id: 2 }],
    }))).toEqual({
      nodes: [{ id: 1 }],
      truncated: true,
    });

    expect(paginateGraphqlConnection({
      pageInfo: { hasNextPage: true, endCursor: 'cursor-1' },
      nodes: [{ id: 1 }],
    }, () => {
      throw new Error('rate limit');
    })).toEqual({
      nodes: [{ id: 1 }],
      truncated: true,
    });
  });
});
