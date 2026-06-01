import { describe, expect, it } from 'vitest';
import {
  collectResolvableReviewThreadIds,
  shouldResolveAutomationOnlyThread,
} from '../../../scripts/ci/lib/review-thread-resolution.mjs';

const actors = new Set(['copilot-pull-request-reviewer', 'chatgpt-codex-connector']);
const handled = new Set([101, 102, 201]);

const thread = (overrides: Record<string, any> = {}) => ({
  id: 'thread-1',
  isResolved: false,
  comments: {
    nodes: [
      { databaseId: 101, author: { login: 'copilot-pull-request-reviewer' } },
      { databaseId: 102, author: { login: 'chatgpt-codex-connector' } },
    ],
  },
  ...overrides,
});

describe('review thread resolution guard', () => {
  it('resolves only unresolved automation-only threads with all comments handled', () => {
    expect(shouldResolveAutomationOnlyThread(thread(), {
      handledCommentIds: handled,
      reviewActorSet: actors,
    })).toBe(true);

    expect(shouldResolveAutomationOnlyThread(thread({ isResolved: true }), {
      handledCommentIds: handled,
      reviewActorSet: actors,
    })).toBe(false);

    expect(shouldResolveAutomationOnlyThread(thread({
      comments: {
        nodes: [
          { databaseId: 101, author: { login: 'copilot-pull-request-reviewer' } },
          { databaseId: 999, author: { login: 'human-reviewer' } },
        ],
      },
    }), {
      handledCommentIds: handled,
      reviewActorSet: actors,
    })).toBe(false);

    expect(shouldResolveAutomationOnlyThread(thread({
      comments: {
        nodes: [
          { databaseId: 101, author: { login: 'copilot-pull-request-reviewer' } },
          { databaseId: 999, author: { login: 'chatgpt-codex-connector' } },
        ],
      },
    }), {
      handledCommentIds: handled,
      reviewActorSet: actors,
    })).toBe(false);

    expect(shouldResolveAutomationOnlyThread(thread({
      comments: {
        pageInfo: { hasNextPage: true },
        nodes: [
          { databaseId: 101, author: { login: 'copilot-pull-request-reviewer' } },
        ],
      },
    }), {
      handledCommentIds: handled,
      reviewActorSet: actors,
    })).toBe(false);
  });

  it('collects resolvable thread ids across paginated thread responses', async () => {
    const pages = [
      {
        nodes: [
          thread({ id: 'thread-1' }),
          thread({
            id: 'mixed-human-thread',
            comments: {
              nodes: [
                { databaseId: 101, author: { login: 'copilot-pull-request-reviewer' } },
                { databaseId: 301, author: { login: 'human-reviewer' } },
              ],
            },
          }),
        ],
        pageInfo: { hasNextPage: true, endCursor: 'cursor-1' },
      },
      {
        nodes: [
          thread({
            id: 'thread-2',
            comments: {
              nodes: [
                { databaseId: 201, author: { login: 'copilot-pull-request-reviewer' } },
              ],
            },
          }),
        ],
        pageInfo: { hasNextPage: false, endCursor: null },
      },
    ];
    const seenCursors: Array<string | null> = [];

    const ids = await collectResolvableReviewThreadIds({
      fetchPage: async (cursor) => {
        seenCursors.push(cursor);
        return pages.shift();
      },
      handledCommentIds: handled,
      reviewActorSet: actors,
    });

    expect(seenCursors).toEqual([null, 'cursor-1']);
    expect(ids).toEqual(['thread-1', 'thread-2']);
  });
});
