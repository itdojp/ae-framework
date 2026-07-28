import { describe, expect, it } from 'vitest';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import {
  captureGitHubWorkState,
  collectPaginated,
  collectSensitiveFieldPaths,
  compareGitHubWorkStateSnapshots,
  compileGitHubWorkStateSchema,
  computeSnapshotDigest,
  resolveAndValidateRepositoryLocalGitHubWorkStateSnapshot,
  stableStringify,
  validateSnapshotSemantics,
} from '../../../scripts/agents/github-work-state-lib.mjs';
import { buildRequiredCheckPolicyFromGitHubResponses } from '../../../scripts/agents/capture-github-work-state.mjs';

const BASE_SHA = 'a'.repeat(40);
const HEAD_SHA = 'b'.repeat(40);

function pageFetcher<T>(items: T[]) {
  return async ({ cursor, pageSize }: { cursor: string | null; pageSize: number }) => {
    const start = cursor === null ? 0 : Number.parseInt(cursor, 10);
    const nodes = items.slice(start, start + pageSize);
    const end = start + nodes.length;
    return {
      totalCount: items.length,
      nodes,
      pageInfo: {
        hasNextPage: end < items.length,
        endCursor: end < items.length ? String(end) : null,
      },
    };
  };
}

function reviewThread(index: number, extra: Record<string, unknown> = {}) {
  return {
    id: `PRRT_thread_${String(index).padStart(4, '0')}`,
    isResolved: index % 2 === 0,
    path: `src/file-${index}.ts`,
    comments: { nodes: [{ id: `PRRC_comment_${String(index).padStart(4, '0')}` }] },
    ...extra,
  };
}

function checkRun(index: number, headSha = HEAD_SHA) {
  return {
    __typename: 'CheckRun',
    name: `required-${String(index).padStart(4, '0')}`,
    status: 'COMPLETED',
    conclusion: 'SUCCESS',
    databaseId: 10_000 + index,
    checkSuite: {
      app: { databaseId: 7 },
      commit: { oid: headSha },
    },
  };
}

function captureOptions({
  threads = [reviewThread(1), reviewThread(2)],
  checks = [checkRun(1), checkRun(2)],
  policy = [
    { name: 'required-0001', appId: 7 },
    { name: 'required-0002', appId: 7 },
  ],
  generatedAt = '2026-07-28T00:00:00.000Z',
} = {}) {
  return {
    repository: 'itdojp/ae-framework',
    issueNumber: 3657,
    pullRequestNumber: 4000,
    generatedAt,
    expectedHead: HEAD_SHA,
    pageSize: 100,
    fetchIssue: async () => ({ number: 3657, state: 'OPEN', stateReason: null }),
    fetchPullRequest: async () => ({
      number: 4000,
      baseRefName: 'main',
      baseRefOid: BASE_SHA,
      headRefName: 'codex/3657-github-authority-snapshot',
      headRefOid: HEAD_SHA,
      isDraft: true,
      mergeStateStatus: 'CLEAN',
      state: 'OPEN',
      merged: false,
      mergeCommit: null,
    }),
    fetchReviewThreadsPage: pageFetcher(threads),
    fetchRequiredChecksPage: pageFetcher(checks),
    fetchRequiredCheckPolicy: async () => Array.isArray(policy)
      ? { source: 'classic-branch-protection', strict: true, checks: policy }
      : policy,
  };
}

async function validSnapshot(options = {}) {
  return captureGitHubWorkState(captureOptions(options));
}

function redigest<T extends Record<string, any>>(snapshot: T): T {
  return {
    ...snapshot,
    snapshotDigest: computeSnapshotDigest(snapshot),
  };
}

function readFixture(name: string) {
  return JSON.parse(readFileSync(resolve('fixtures/github-work-state', name), 'utf8'));
}

describe('GitHub work-state authority contract', () => {
  it('validates its own schema and a captured snapshot', async () => {
    const snapshot = await validSnapshot();
    const validate = compileGitHubWorkStateSchema();
    expect(validate(snapshot), JSON.stringify(validate.errors)).toBe(true);
    expect(validateSnapshotSemantics(snapshot)).toEqual([]);
    expect(snapshot.snapshotDigest).toMatch(/^sha256:[a-f0-9]{64}$/u);
  });

  it('replays committed offline stale/no-op/wrong-head fixtures', () => {
    const baseline = readFixture('sample.github-work-state.json');
    const sameState = readFixture('same-state-later.github-work-state.json');
    const staleHead = readFixture('stale-head.github-work-state.json');
    const changedIds = readFixture('same-count-different-thread-ids.github-work-state.json');
    const wrongHeadCheck = readFixture('wrong-head-check.github-work-state.json');

    expect(compareGitHubWorkStateSnapshots(baseline, sameState, { expectedHead: HEAD_SHA }).status)
      .toBe('no-state-change');
    expect(compareGitHubWorkStateSnapshots(baseline, staleHead, { expectedHead: 'c'.repeat(40) }).status)
      .toBe('stale-context');
    expect(compareGitHubWorkStateSnapshots(baseline, changedIds, { expectedHead: HEAD_SHA }).status)
      .toBe('stale-context');
    expect(compareGitHubWorkStateSnapshots(baseline, wrongHeadCheck, { expectedHead: HEAD_SHA }).status)
      .toBe('contract-invalid');
  });

  it('exposes deterministic offline validator exit codes', () => {
    const localTmp = resolve('.codex-local/tmp');
    mkdirSync(localTmp, { recursive: true });
    const outputRoot = mkdtempSync(resolve(localTmp, 'github-work-state-compare-'));
    const script = resolve('scripts/agents/compare-github-work-state.mjs');
    const baseline = resolve('fixtures/github-work-state/sample.github-work-state.json');
    const cases = [
      ['same-state-later.github-work-state.json', HEAD_SHA, 0, 'no-state-change'],
      ['same-count-different-thread-ids.github-work-state.json', HEAD_SHA, 2, 'stale-context'],
      ['wrong-head-check.github-work-state.json', HEAD_SHA, 1, 'contract-invalid'],
    ] as const;
    try {
      for (const [fixture, expectedHead, expectedExit, expectedStatus] of cases) {
        const output = resolve(outputRoot, `${expectedStatus}.json`);
        const result = spawnSync(process.execPath, [
          script,
          '--baseline', baseline,
          '--current', resolve('fixtures/github-work-state', fixture),
          '--expected-head', expectedHead,
          '--output', output,
        ], { encoding: 'utf8' });
        expect(result.status, result.stderr).toBe(expectedExit);
        expect(JSON.parse(readFileSync(output, 'utf8')).status).toBe(expectedStatus);
      }
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('captures more than 100 GraphQL review threads and checks across every page', async () => {
    const threads = Array.from({ length: 205 }, (_, index) => reviewThread(index + 1));
    const checks = Array.from({ length: 205 }, (_, index) => checkRun(index + 1));
    const policy = checks.map((entry) => ({ name: entry.name, appId: 7 }));
    const snapshot = await validSnapshot({ threads, checks, policy });

    expect(snapshot.reviewThreads).toHaveLength(205);
    expect(snapshot.requiredChecks).toHaveLength(205);
    expect(snapshot.pagination.reviewThreads).toMatchObject({
      pagesFetched: 3,
      totalCount: 205,
      capturedCount: 205,
      complete: true,
    });
    expect(snapshot.pagination.requiredChecks).toMatchObject({
      pagesFetched: 3,
      totalCount: 205,
      capturedCount: 205,
      complete: true,
    });
  });

  it('fails closed when pagination is incomplete or cannot advance', async () => {
    await expect(collectPaginated(async () => ({
      totalCount: 2,
      nodes: [{ id: 1 }],
      pageInfo: { hasNextPage: false, endCursor: null },
    }), { label: 'incomplete' })).rejects.toThrow('captured 1 of 2');

    await expect(collectPaginated(async () => ({
      totalCount: 2,
      nodes: [{ id: 1 }],
      pageInfo: { hasNextPage: true, endCursor: null },
    }), { label: 'missing-cursor' })).rejects.toThrow('without an endCursor');
  });

  it('rejects cursor cycles, duplicate pages/nodes, empty continuing pages, and total overflow', async () => {
    let sameCursorCalls = 0;
    await expect(collectPaginated(async () => {
      sameCursorCalls += 1;
      return {
        totalCount: 2,
        nodes: [{ id: `node-${sameCursorCalls}` }],
        pageInfo: { hasNextPage: true, endCursor: 'A' },
      };
    }, { label: 'same-cursor' })).rejects.toThrow('cursor cycle');

    const cyclePages = [
      { nodes: [{ id: 'one' }], endCursor: 'A' },
      { nodes: [{ id: 'two' }], endCursor: 'B' },
      { nodes: [{ id: 'three' }], endCursor: 'A' },
    ];
    let cycleIndex = 0;
    await expect(collectPaginated(async () => {
      const page = cyclePages[cycleIndex++];
      return {
        totalCount: 4,
        nodes: page.nodes,
        pageInfo: { hasNextPage: true, endCursor: page.endCursor },
      };
    }, { label: 'cursor-cycle' })).rejects.toThrow('cursor cycle');

    let duplicatePageIndex = 0;
    await expect(collectPaginated(async () => ({
      totalCount: 2,
      nodes: [{ id: 'same-node' }],
      pageInfo: { hasNextPage: duplicatePageIndex++ === 0, endCursor: 'fresh-cursor' },
    }), { label: 'duplicate-page' })).rejects.toThrow(/duplicate (?:page|node)/u);

    await expect(collectPaginated(async () => ({
      totalCount: 1,
      nodes: [],
      pageInfo: { hasNextPage: true, endCursor: 'next' },
    }), { label: 'empty-page' })).rejects.toThrow('yielded no new nodes');

    await expect(collectPaginated(async () => ({
      totalCount: 1,
      nodes: [{ id: 'one' }, { id: 'two' }],
      pageInfo: { hasNextPage: false, endCursor: null },
    }), { label: 'overflow' })).rejects.toThrow('exceeds declared total');

    let boundedPage = 0;
    await expect(collectPaginated(async () => ({
      totalCount: 3,
      nodes: [{ id: `bounded-${boundedPage}` }],
      pageInfo: { hasNextPage: true, endCursor: `cursor-${boundedPage++}` },
    }), { label: 'bounded', maxPages: 2 })).rejects.toThrow('maximum page count 2');
  });

  it('uses the complete thread ID set rather than the unresolved count', async () => {
    const baseline = await validSnapshot();
    const current = structuredClone(baseline);
    current.generatedAt = '2026-07-28T01:00:00.000Z';
    current.reviewThreads = [
      { ...current.reviewThreads[0], threadId: 'PRRT_replacement', topCommentId: 'PRRC_replacement' },
      current.reviewThreads[1],
    ].sort((left, right) => left.threadId.localeCompare(right.threadId));
    current.snapshotDigest = computeSnapshotDigest(current);

    const baselineUnresolved = baseline.reviewThreads.filter((thread) => !thread.isResolved).length;
    const currentUnresolved = current.reviewThreads.filter((thread) => !thread.isResolved).length;
    expect(currentUnresolved).toBe(baselineUnresolved);

    const result = compareGitHubWorkStateSnapshots(baseline, current, { expectedHead: HEAD_SHA });
    expect(result.status).toBe('stale-context');
    expect(result.changes.map((entry: { kind: string }) => entry.kind)).toContain('review-thread-set-changed');
  });

  it('classifies a stale PR head and a required-check rerun', async () => {
    const baseline = await validSnapshot();
    const staleHead = structuredClone(baseline);
    const nextHead = 'c'.repeat(40);
    staleHead.headSha = nextHead;
    staleHead.requiredChecks = staleHead.requiredChecks.map((check) => ({ ...check, headSha: nextHead }));
    staleHead.snapshotDigest = computeSnapshotDigest(staleHead);
    const headResult = compareGitHubWorkStateSnapshots(baseline, staleHead, { expectedHead: nextHead });
    expect(headResult.status).toBe('stale-context');
    expect(headResult.changes.map((entry: { kind: string }) => entry.kind)).toContain('head-changed');

    const rerun = structuredClone(baseline);
    rerun.requiredChecks[0].runId = '999999';
    rerun.snapshotDigest = computeSnapshotDigest(rerun);
    const rerunResult = compareGitHubWorkStateSnapshots(baseline, rerun, { expectedHead: HEAD_SHA });
    expect(rerunResult.status).toBe('stale-context');
    expect(rerunResult.changes.map((entry: { kind: string }) => entry.kind)).toContain('required-check-rerun');
  });

  it('classifies a changed base authority without conflating it with capture time', async () => {
    const baseline = await validSnapshot();
    const current = structuredClone(baseline);
    current.baseSha = 'f'.repeat(40);
    current.generatedAt = '2026-07-29T00:00:00.000Z';
    current.snapshotDigest = computeSnapshotDigest(current);
    const result = compareGitHubWorkStateSnapshots(baseline, current, { expectedHead: HEAD_SHA });
    expect(result.status).toBe('stale-context');
    expect(result.changes.map((entry: { kind: string }) => entry.kind)).toContain('base-changed');
  });

  it('classifies repeated semantic state as no-state-change despite capture-time differences', async () => {
    const baseline = await validSnapshot({ generatedAt: '2026-07-28T00:00:00.000Z' });
    const current = await validSnapshot({ generatedAt: '2026-08-01T12:34:56.000Z' });
    expect(current.snapshotDigest).toBe(baseline.snapshotDigest);
    expect(compareGitHubWorkStateSnapshots(baseline, current, { expectedHead: HEAD_SHA })).toMatchObject({
      status: 'no-state-change',
      changes: [],
    });
  });

  it('requires two stable semantic passes and retries transient thread/check changes', async () => {
    const options = captureOptions();
    let threadCalls = 0;
    let checkCalls = 0;
    const threadStates = [
      [reviewThread(1)],
      [{ ...reviewThread(1), isResolved: true }],
      [{ ...reviewThread(1), isResolved: true }],
      [{ ...reviewThread(1), isResolved: true }],
    ];
    const checkStates = [
      [checkRun(1)],
      [{ ...checkRun(1), conclusion: 'PENDING' }],
      [{ ...checkRun(1), conclusion: 'PENDING' }],
      [{ ...checkRun(1), conclusion: 'PENDING' }],
    ];
    const snapshot = await captureGitHubWorkState({
      ...options,
      fetchReviewThreadsPage: async () => {
        const nodes = threadStates[Math.min(threadCalls++, threadStates.length - 1)];
        return { totalCount: nodes.length, nodes, pageInfo: { hasNextPage: false, endCursor: null } };
      },
      fetchRequiredChecksPage: async () => {
        const nodes = checkStates[Math.min(checkCalls++, checkStates.length - 1)];
        return { totalCount: nodes.length, nodes, pageInfo: { hasNextPage: false, endCursor: null } };
      },
      fetchRequiredCheckPolicy: async () => ({
        source: 'classic-branch-protection',
        strict: true,
        checks: [{ name: 'required-0001', appId: 7 }],
      }),
    });
    expect(threadCalls).toBe(4);
    expect(checkCalls).toBe(4);
    expect(snapshot.reviewThreads[0].isResolved).toBe(true);
    expect(snapshot.requiredChecks[0].conclusion).toBe('PENDING');
  });

  it('retries transient pagination consistency failures before accepting two stable passes', async () => {
    const scenarios = [
      {
        name: 'totalCount change',
        pages: [
          {
            totalCount: 2,
            nodes: [reviewThread(1)],
            pageInfo: { hasNextPage: true, endCursor: 'total-next' },
          },
          {
            totalCount: 3,
            nodes: [reviewThread(2)],
            pageInfo: { hasNextPage: false, endCursor: null },
          },
        ],
      },
      {
        name: 'duplicate node',
        pages: [
          {
            totalCount: 3,
            nodes: [reviewThread(1)],
            pageInfo: { hasNextPage: true, endCursor: 'duplicate-next' },
          },
          {
            totalCount: 3,
            nodes: [reviewThread(2), reviewThread(1)],
            pageInfo: { hasNextPage: false, endCursor: null },
          },
        ],
      },
      {
        name: 'total overflow',
        pages: [{
          totalCount: 1,
          nodes: [reviewThread(1), reviewThread(2)],
          pageInfo: { hasNextPage: false, endCursor: null },
        }],
      },
      {
        name: 'incomplete pagination',
        pages: [{
          totalCount: 2,
          nodes: [reviewThread(1)],
          pageInfo: { hasNextPage: false, endCursor: null },
        }],
      },
    ];

    for (const scenario of scenarios) {
      const options = captureOptions();
      let transientPageIndex = 0;
      let calls = 0;
      const snapshot = await captureGitHubWorkState({
        ...options,
        consistencyAttempts: 2,
        fetchReviewThreadsPage: async () => {
          calls += 1;
          if (transientPageIndex < scenario.pages.length) {
            return scenario.pages[transientPageIndex++];
          }
          const nodes = [reviewThread(9)];
          return { totalCount: nodes.length, nodes, pageInfo: { hasNextPage: false, endCursor: null } };
        },
      });
      expect(snapshot.reviewThreads.map((thread) => thread.threadId), scenario.name)
        .toEqual([reviewThread(9).id]);
      expect(calls, scenario.name).toBe(scenario.pages.length + 2);
    }
  });

  it('fails closed after retrying persistent pagination consistency failures', async () => {
    const options = captureOptions();
    let calls = 0;
    await expect(captureGitHubWorkState({
      ...options,
      consistencyAttempts: 2,
      fetchReviewThreadsPage: async () => {
        calls += 1;
        return {
          totalCount: 2,
          nodes: [reviewThread(1)],
          pageInfo: { hasNextPage: false, endCursor: null },
        };
      },
    })).rejects.toThrow('did not stabilize after 2 attempts');
    expect(calls).toBe(2);
  });

  it('applies pagination consistency retries to required-check collection', async () => {
    const options = captureOptions({
      checks: [checkRun(1)],
      policy: [{ name: 'required-0001', appId: 7 }],
    });
    let calls = 0;
    const snapshot = await captureGitHubWorkState({
      ...options,
      consistencyAttempts: 2,
      fetchRequiredChecksPage: async () => {
        calls += 1;
        if (calls === 1) {
          return {
            totalCount: 2,
            nodes: [checkRun(1)],
            pageInfo: { hasNextPage: true, endCursor: 'checks-next' },
          };
        }
        if (calls === 2) {
          return {
            totalCount: 3,
            nodes: [checkRun(2)],
            pageInfo: { hasNextPage: false, endCursor: null },
          };
        }
        const nodes = [checkRun(1)];
        return { totalCount: nodes.length, nodes, pageInfo: { hasNextPage: false, endCursor: null } };
      },
    });
    expect(calls).toBe(4);
    expect(snapshot.requiredChecks.map((check) => check.name)).toEqual(['required-0001']);
  });

  it('accepts an explicitly stable two-pass capture and rejects check-only instability', async () => {
    const options = captureOptions();
    let stableCheckCalls = 0;
    const stable = await captureGitHubWorkState({
      ...options,
      fetchRequiredChecksPage: async (args) => {
        stableCheckCalls += 1;
        return pageFetcher([checkRun(1), checkRun(2)])(args);
      },
    });
    expect(stableCheckCalls).toBe(2);
    expect(stable.requiredChecks).toHaveLength(2);

    let changingCheckCalls = 0;
    await expect(captureGitHubWorkState({
      ...options,
      consistencyAttempts: 2,
      fetchRequiredChecksPage: async () => {
        const conclusion = changingCheckCalls++ % 2 === 0 ? 'SUCCESS' : 'PENDING';
        const nodes = [{ ...checkRun(1), conclusion }, checkRun(2)];
        return { totalCount: nodes.length, nodes, pageInfo: { hasNextPage: false, endCursor: null } };
      },
    })).rejects.toThrow('did not stabilize after 2 attempts');
  });

  it('fails closed when the authority head changes during capture or semantic state never stabilizes', async () => {
    const options = captureOptions();
    let pullRequestCalls = 0;
    const basePullRequest = await options.fetchPullRequest();
    await expect(captureGitHubWorkState({
      ...options,
      consistencyAttempts: 1,
      fetchPullRequest: async () => ({
        ...basePullRequest,
        headRefOid: pullRequestCalls++ % 2 === 0 ? HEAD_SHA : 'c'.repeat(40),
      }),
    })).rejects.toThrow('authority-state-changed-during-capture');

    let threadCalls = 0;
    await expect(captureGitHubWorkState({
      ...options,
      consistencyAttempts: 3,
      fetchReviewThreadsPage: async () => {
        const node = { ...reviewThread(1), isResolved: threadCalls++ % 2 === 0 };
        return { totalCount: 1, nodes: [node], pageInfo: { hasNextPage: false, endCursor: null } };
      },
      fetchRequiredCheckPolicy: async () => ({
        source: 'classic-branch-protection', strict: true, checks: [
          { name: 'required-0001', appId: 7 },
          { name: 'required-0002', appId: 7 },
        ],
      }),
    })).rejects.toThrow('did not stabilize after 3 attempts');
  });

  it('includes strict required-check policy and check/app changes in stale-context classification', async () => {
    const baseline = await validSnapshot();
    const mutations = [
      { policy: { ...baseline.requiredCheckPolicy, strict: false }, appId: null },
      {
        policy: { ...baseline.requiredCheckPolicy, checks: baseline.requiredCheckPolicy.checks.slice(0, 1) },
        appId: null,
      },
      {
        policy: {
          ...baseline.requiredCheckPolicy,
          checks: baseline.requiredCheckPolicy.checks.map((entry) => ({ ...entry, appId: 99 })),
        },
        appId: 99,
      },
    ];
    for (const { policy: requiredCheckPolicy, appId } of mutations) {
      const current = structuredClone(baseline);
      current.requiredCheckPolicy = requiredCheckPolicy;
      if (requiredCheckPolicy.checks.length !== current.requiredChecks.length) {
        current.requiredChecks = current.requiredChecks.slice(0, requiredCheckPolicy.checks.length);
      } else if (appId !== null) {
        current.requiredChecks = current.requiredChecks.map((entry) => ({ ...entry, appId }));
      }
      current.snapshotDigest = computeSnapshotDigest(current);
      const result = compareGitHubWorkStateSnapshots(baseline, current, { expectedHead: HEAD_SHA });
      expect(result.status).toBe('stale-context');
      expect(result.changes.map((entry: { kind: string }) => entry.kind))
        .toContain('required-check-policy-changed');
    }

    const noChecks = await validSnapshot({ checks: [], policy: [] });
    expect(noChecks.requiredCheckPolicy).toMatchObject({ strict: true, checks: [] });
    expect(noChecks.requiredChecks).toEqual([]);
    await expect(validSnapshot({ policy: { source: 'classic-branch-protection', checks: [] } }))
      .rejects.toThrow('strict must be boolean');
    await expect(validSnapshot({ policy: { source: 'ruleset', strict: true, checks: [] } }))
      .rejects.toThrow('source must be classic-branch-protection');
    await expect(validSnapshot({
      policy: {
        source: 'classic-branch-protection',
        strict: true,
        checks: [{ name: 'required-0001', appId: 'unbound' }],
      },
    })).rejects.toThrow('appId must be a positive integer or null');
  });

  it('fails closed on active rulesets and malformed classic branch-protection policy', () => {
    expect(buildRequiredCheckPolicyFromGitHubResponses([], null)).toEqual({
      source: 'classic-branch-protection', strict: false, checks: [],
    });
    expect(buildRequiredCheckPolicyFromGitHubResponses([], {
      strict: true,
      checks: [{ context: 'verify-lite', app_id: 15368 }],
      contexts: ['verify-lite', 'legacy'],
    })).toEqual({
      source: 'classic-branch-protection',
      strict: true,
      checks: [
        { name: 'verify-lite', appId: 15368 },
        { name: 'legacy', appId: null },
      ],
    });
    expect(() => buildRequiredCheckPolicyFromGitHubResponses(
      [{ type: 'required_status_checks' }],
      null,
    )).toThrow('a ruleset applies');
    expect(() => buildRequiredCheckPolicyFromGitHubResponses([], { checks: [] }))
      .toThrow('response is malformed');
    expect(() => buildRequiredCheckPolicyFromGitHubResponses({}, null))
      .toThrow('effective rules response is malformed');
  });

  it('captures and classifies Issue/PR lifecycle changes and merge commit binding', async () => {
    const baseline = await validSnapshot();
    const mergedCaptured = await captureGitHubWorkState({
      ...captureOptions(),
      fetchIssue: async () => ({ number: 3657, state: 'CLOSED', stateReason: 'COMPLETED' }),
      fetchPullRequest: async () => ({
        number: 4000,
        baseRefName: 'main',
        baseRefOid: BASE_SHA,
        headRefName: 'codex/3657-github-authority-snapshot',
        headRefOid: HEAD_SHA,
        isDraft: false,
        mergeStateStatus: 'UNKNOWN',
        state: 'MERGED',
        merged: true,
        mergeCommit: { oid: 'e'.repeat(40) },
      }),
    });
    expect(mergedCaptured).toMatchObject({
      issueState: 'CLOSED',
      issueStateReason: 'COMPLETED',
      pullRequestState: 'MERGED',
      merged: true,
      mergeCommitSha: 'e'.repeat(40),
    });

    for (const reason of ['COMPLETED', 'NOT_PLANNED']) {
      const closed = structuredClone(baseline);
      closed.issueState = 'CLOSED';
      closed.issueStateReason = reason;
      closed.snapshotDigest = computeSnapshotDigest(closed);
      const result = compareGitHubWorkStateSnapshots(baseline, closed, { expectedHead: HEAD_SHA });
      expect(result.changes.map((entry: { kind: string }) => entry.kind)).toContain('issue-state-changed');
    }

    const closedPr = redigest({ ...structuredClone(baseline), pullRequestState: 'CLOSED' });
    expect(compareGitHubWorkStateSnapshots(baseline, closedPr, { expectedHead: HEAD_SHA }).changes
      .map((entry: { kind: string }) => entry.kind)).toContain('pull-request-state-changed');

    const mergeSha = 'e'.repeat(40);
    const mergedPr = redigest({
      ...structuredClone(baseline),
      pullRequestState: 'MERGED',
      merged: true,
      mergeCommitSha: mergeSha,
    });
    const mergedResult = compareGitHubWorkStateSnapshots(baseline, mergedPr, { expectedHead: HEAD_SHA });
    expect(mergedResult.changes.map((entry: { kind: string }) => entry.kind))
      .toEqual(expect.arrayContaining(['pull-request-state-changed', 'pull-request-merged']));

    const missingMergeBinding = redigest({ ...mergedPr, mergeCommitSha: null });
    expect(validateSnapshotSemantics(missingMergeBinding)).toContain('merged PR must bind mergeCommitSha');
  });

  it('does not treat a successful required check from another head as current success', async () => {
    const wrongHeadCheck = checkRun(1, 'd'.repeat(40));
    const snapshot = await validSnapshot({
      checks: [wrongHeadCheck],
      policy: [{ name: wrongHeadCheck.name, appId: 7 }],
    });
    expect(snapshot.requiredChecks).toEqual([
      expect.objectContaining({
        name: wrongHeadCheck.name,
        conclusion: 'MISSING',
        sourceType: 'missing',
        headSha: HEAD_SHA,
      }),
    ]);

    const tampered = structuredClone(snapshot);
    tampered.requiredChecks[0] = {
      name: wrongHeadCheck.name,
      conclusion: 'SUCCESS',
      runId: '10001',
      headSha: 'd'.repeat(40),
      sourceType: 'check-run',
      appId: 7,
    };
    tampered.snapshotDigest = computeSnapshotDigest(tampered);
    expect(validateSnapshotSemantics(tampered)).toContain(
      `required check ${wrongHeadCheck.name} is bound to wrong head ${'d'.repeat(40)}`,
    );
    expect(compareGitHubWorkStateSnapshots(snapshot, tampered, { expectedHead: HEAD_SHA }).status)
      .toBe('contract-invalid');
  });

  it('does not copy review bodies, tokens, or source-only sensitive fields into a snapshot', async () => {
    const sourceThread = reviewThread(1, {
      body: 'synthetic private review body',
      token: 'synthetic-token',
      comments: {
        nodes: [{
          id: 'PRRC_comment_0001',
          bodyText: 'synthetic comment body',
          secret: 'synthetic-secret',
        }],
      },
    });
    const snapshot = await validSnapshot({
      threads: [sourceThread],
      checks: [checkRun(1)],
      policy: [{ name: 'required-0001', appId: 7 }],
    });
    expect(collectSensitiveFieldPaths(snapshot)).toEqual([]);
    expect(JSON.stringify(snapshot)).not.toContain('synthetic private review body');
    expect(JSON.stringify(snapshot)).not.toContain('synthetic-token');
    expect(JSON.stringify(snapshot)).not.toContain('synthetic-secret');
  });

  it('produces byte-identical canonical JSON for identical capture inputs', async () => {
    const first = await validSnapshot();
    const second = await validSnapshot();
    expect(stableStringify(first)).toBe(stableStringify(second));
    expect(`${JSON.stringify(first, null, 2)}\n`).toBe(`${JSON.stringify(second, null, 2)}\n`);
  });

  it('fails schema and semantic validation for unknown fields or digest mutation', async () => {
    const snapshot = await validSnapshot();
    const withReviewBody = { ...snapshot, reviewBody: 'must not be stored' };
    const validate = compileGitHubWorkStateSchema();
    expect(validate(withReviewBody)).toBe(false);

    const digestMutation = { ...snapshot, snapshotDigest: `sha256:${'0'.repeat(64)}` };
    expect(validateSnapshotSemantics(digestMutation)).toContain(
      'snapshotDigest does not match the semantic snapshot content',
    );
  });

  it('fails capture when the authority head differs from the expected exact head', async () => {
    await expect(captureGitHubWorkState({
      ...captureOptions(),
      expectedHead: 'e'.repeat(40),
    })).rejects.toThrow('stale head');
  });

  it('keeps canonical redigest helper semantically valid', async () => {
    const snapshot = await validSnapshot();
    const clone = redigest({ ...snapshot, generatedAt: '2026-07-29T00:00:00.000Z' });
    expect(validateSnapshotSemantics(clone)).toEqual([]);
  });

  it('validates only repository-local regular non-symlink snapshot references', () => {
    const localTmp = resolve('.codex-local/tmp');
    mkdirSync(localTmp, { recursive: true });
    const repoRoot = mkdtempSync(resolve(localTmp, 'authority-reference-'));
    const authorityDir = resolve(repoRoot, '.codex-local/authority');
    mkdirSync(authorityDir, { recursive: true });
    const fixture = readFixture('sample.github-work-state.json');
    const relativePath = '.codex-local/authority/current.json';
    writeFileSync(resolve(repoRoot, relativePath), `${JSON.stringify(fixture)}\n`);
    try {
      const validated = resolveAndValidateRepositoryLocalGitHubWorkStateSnapshot(relativePath, {
        repoRoot,
        expectedDigest: fixture.snapshotDigest,
      });
      expect(validated.snapshot.snapshotDigest).toBe(fixture.snapshotDigest);

      expect(() => resolveAndValidateRepositoryLocalGitHubWorkStateSnapshot('missing.json', { repoRoot }))
        .toThrow('does not exist');
      expect(() => resolveAndValidateRepositoryLocalGitHubWorkStateSnapshot(resolve(repoRoot, relativePath), { repoRoot }))
        .toThrow('repository-relative');

      writeFileSync(resolve(authorityDir, 'malformed.json'), '{invalid');
      expect(() => resolveAndValidateRepositoryLocalGitHubWorkStateSnapshot(
        '.codex-local/authority/malformed.json',
        { repoRoot },
      )).toThrow('not valid JSON');
      expect(() => resolveAndValidateRepositoryLocalGitHubWorkStateSnapshot(relativePath, {
        repoRoot,
        expectedDigest: `sha256:${'0'.repeat(64)}`,
      })).toThrow('does not match');

      symlinkSync(resolve(repoRoot, relativePath), resolve(authorityDir, 'link.json'));
      expect(() => resolveAndValidateRepositoryLocalGitHubWorkStateSnapshot(
        '.codex-local/authority/link.json',
        { repoRoot },
      )).toThrow('symbolic links are forbidden');
    } finally {
      rmSync(repoRoot, { recursive: true, force: true });
    }
  });
});
