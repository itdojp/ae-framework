import { describe, expect, it } from 'vitest';
import {
  resolveGateResult,
  resolvePrContext,
  truncateUnicodeSafe,
} from '../../../scripts/ci/copilot-review-gate.mjs';
import { toActorSet } from '../../../scripts/ci/lib/automation-guards.mjs';

describe('copilot-review-gate helpers', () => {
  it('resolves PR context from explicit env, payload, and event type', () => {
    const contextFromExplicit = resolvePrContext({
      eventName: 'workflow_dispatch',
      eventPayload: {
        repository: { default_branch: 'main' },
      },
      explicitPrNumber: 42,
      githubRef: 'refs/heads/main',
    });
    expect(contextFromExplicit.number).toBe(42);
    expect(contextFromExplicit.isDefaultBranch).toBe(true);

    const contextFromPayload = resolvePrContext({
      eventName: 'pull_request',
      eventPayload: {
        pull_request: { number: 77 },
        repository: { default_branch: 'main' },
      },
      explicitPrNumber: null,
      githubRef: 'refs/heads/feature',
    });
    expect(contextFromPayload.number).toBe(77);
    expect(contextFromPayload.isDefaultBranch).toBe(false);

    const issueCommentWithoutPr = resolvePrContext({
      eventName: 'issue_comment',
      eventPayload: {
        issue: { number: 100 },
      },
      explicitPrNumber: null,
      githubRef: 'refs/heads/main',
    });
    expect(issueCommentWithoutPr.isIssueCommentWithoutPr).toBe(true);
  });

  it('detects review presence and unresolved actor threads', () => {
    const actorSet = toActorSet(['github-copilot[bot]', 'copilot']);
    const result = resolveGateResult({
      reviews: {
        nodes: [
          { author: { login: 'octocat' }, state: 'COMMENTED' },
          { author: { login: 'github-copilot[bot]' }, state: 'COMMENTED' },
        ],
      },
      reviewThreads: {
        nodes: [
          {
            isResolved: false,
            comments: {
              nodes: [
                { author: { login: 'github-copilot[bot]' }, bodyText: 'Fix variable naming.' },
              ],
            },
          },
          {
            isResolved: true,
            comments: {
              nodes: [
                { author: { login: 'copilot' }, bodyText: 'Looks good.' },
              ],
            },
          },
        ],
      },
    }, actorSet);

    expect(result.hasReview).toBe(true);
    expect(result.actorThreadsCount).toBe(2);
    expect(result.unresolvedThreadsCount).toBe(1);
    expect(result.unresolvedSummaries[0]).toContain('Thread 1');
  });

  it('ignores non-actor threads', () => {
    const actorSet = toActorSet(['github-copilot[bot]']);
    const result = resolveGateResult({
      reviews: {
        nodes: [{ author: { login: 'octocat' }, state: 'COMMENTED' }],
      },
      reviewThreads: {
        nodes: [
          {
            isResolved: false,
            comments: {
              nodes: [{ author: { login: 'octocat' }, bodyText: 'Needs change.' }],
            },
          },
        ],
      },
    }, actorSet);

    expect(result.hasReview).toBe(false);
    expect(result.actorThreadsCount).toBe(0);
    expect(result.unresolvedThreadsCount).toBe(0);
  });

  it('truncates unicode text safely', () => {
    expect(truncateUnicodeSafe('  abc  def  ', 7)).toBe('abc def');
    expect(truncateUnicodeSafe('abc😀defghi', 8)).toBe('abc😀d...');
    expect(truncateUnicodeSafe('abc', 0)).toBe('');
  });
});
