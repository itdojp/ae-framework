import { describe, expect, it } from 'vitest';
import { mkdirSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import {
  captureGitHubWorkState,
  collectPaginated,
  collectSensitiveFieldPaths,
  compareGitHubWorkStateSnapshots,
  compileGitHubWorkStateSchema,
  computeSnapshotDigest,
  stableStringify,
  validateSnapshotSemantics,
} from '../../../scripts/agents/github-work-state-lib.mjs';

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
    fetchIssue: async () => ({ number: 3657 }),
    fetchPullRequest: async () => ({
      number: 4000,
      baseRefName: 'main',
      baseRefOid: BASE_SHA,
      headRefName: 'codex/3657-github-authority-snapshot',
      headRefOid: HEAD_SHA,
      isDraft: true,
      mergeStateStatus: 'CLEAN',
    }),
    fetchReviewThreadsPage: pageFetcher(threads),
    fetchRequiredChecksPage: pageFetcher(checks),
    fetchRequiredCheckPolicy: async () => policy,
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
});
