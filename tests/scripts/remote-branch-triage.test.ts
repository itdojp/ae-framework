import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const triageScript = resolve(repoRoot, 'scripts/maintenance/remote-branch-triage.mjs');
const triageModuleUrl = pathToFileURL(triageScript).href;

const buildPullRequestLookup = (items: Array<Record<string, unknown>>) => {
  const sorted = [...items].sort((a, b) =>
    String(b.updatedAt || b.mergedAt || b.closedAt || '').localeCompare(
      String(a.updatedAt || a.mergedAt || a.closedAt || ''),
    ),
  );
  const byHeadRefName = new Map<string, Array<Record<string, unknown>>>();
  for (const item of sorted) {
    const headRefName = String(item.headRefName || '');
    if (!headRefName) continue;
    const current = byHeadRefName.get(headRefName) || [];
    current.push(item);
    byHeadRefName.set(headRefName, current);
  }
  return {
    available: true,
    disabled: false,
    reason: '',
    requestedBaseBranch: '',
    requestedLimit: 1000,
    items: sorted,
    byHeadRefName,
  };
};

describe.sequential('remote-branch-triage script', () => {
  it('filters cross-repository PRs when repository identity is provided', async () => {
    const mod = await import(triageModuleUrl);
    const report = mod.loadPullRequests(
      {
        limit: 10,
        baseBranch: 'main',
        repositoryOwner: 'itdojp',
        repositoryName: 'ae-framework',
      },
      {
        ghRunner: () => ({
          ok: true,
          output: JSON.stringify([
            {
              number: 10,
              title: 'same repo branch',
              url: 'https://example.test/pr/10',
              state: 'MERGED',
              isDraft: false,
              mergedAt: '2026-03-06T09:00:00Z',
              closedAt: '2026-03-06T09:00:00Z',
              updatedAt: '2026-03-06T09:00:00Z',
              headRefName: 'feat/shared-name',
              headRefOid: 'aaaa',
              baseRefName: 'main',
              headRepository: { name: 'ae-framework' },
              headRepositoryOwner: { login: 'itdojp' },
            },
            {
              number: 11,
              title: 'fork branch with same name',
              url: 'https://example.test/pr/11',
              state: 'OPEN',
              isDraft: false,
              mergedAt: '',
              closedAt: '',
              updatedAt: '2026-03-06T10:00:00Z',
              headRefName: 'feat/shared-name',
              headRefOid: 'bbbb',
              baseRefName: 'main',
              headRepository: { name: 'forked-ae-framework' },
              headRepositoryOwner: { login: 'external-user' },
            },
          ]),
        }),
      },
    );

    expect(report.available).toBe(true);
    expect(report.items).toHaveLength(1);
    expect(report.items[0]).toEqual(
      expect.objectContaining({
        number: 10,
        headRefName: 'feat/shared-name',
        headRefOid: 'aaaa',
      }),
    );
    expect(report.byHeadRefName.get('feat/shared-name')).toHaveLength(1);
  });

  it('builds a structured report with PR linkage and triage classifications', async () => {
    const mod = await import(triageModuleUrl);
    const report = mod.buildTriageReport(
      {
        generatedAt: '2026-03-06T10:00:00Z',
        base: 'origin/main',
        remote: 'origin',
        candidates: {
          remoteMerged: ['docs/merged-a'],
          remoteStaleByAge: [
            { branch: 'docs/stale-a', ageDays: 160 },
            { branch: 'feat/stale-b', ageDays: 200 },
            { branch: 'feat/open-c', ageDays: 95 },
            { branch: 'ci/stale-d', ageDays: 140 },
          ],
        },
      },
      {
        generatedAt: '2026-03-06T11:00:00Z',
        inputJsonPath: 'tmp/maintenance/branch-inventory.json',
        pullRequests: buildPullRequestLookup([
          {
            number: 2466,
            title: 'merged docs cleanup',
            url: 'https://example.test/pr/2466',
            state: 'merged',
            isDraft: false,
            mergedAt: '2026-03-06T09:00:00Z',
            closedAt: '2026-03-06T09:00:00Z',
            updatedAt: '2026-03-06T09:00:00Z',
            headRefName: 'docs/merged-a',
            baseRefName: 'main',
          },
          {
            number: 2401,
            title: 'closed docs experiment',
            url: 'https://example.test/pr/2401',
            state: 'closed',
            isDraft: false,
            mergedAt: '',
            closedAt: '2026-03-01T09:00:00Z',
            updatedAt: '2026-03-01T09:00:00Z',
            headRefName: 'docs/stale-a',
            baseRefName: 'main',
          },
          {
            number: 2398,
            title: 'first feature attempt',
            url: 'https://example.test/pr/2398',
            state: 'closed',
            isDraft: false,
            mergedAt: '',
            closedAt: '2026-03-04T09:00:00Z',
            updatedAt: '2026-03-04T09:00:00Z',
            headRefName: 'feat/stale-b',
            baseRefName: 'main',
          },
          {
            number: 2399,
            title: 'second feature attempt',
            url: 'https://example.test/pr/2399',
            state: 'merged',
            isDraft: false,
            mergedAt: '2026-03-05T12:00:00Z',
            closedAt: '2026-03-05T12:00:00Z',
            updatedAt: '2026-03-05T12:00:00Z',
            headRefName: 'feat/stale-b',
            baseRefName: 'main',
          },
          {
            number: 2400,
            title: 'open feature work',
            url: 'https://example.test/pr/2400',
            state: 'open',
            isDraft: false,
            mergedAt: '',
            closedAt: '',
            updatedAt: '2026-03-05T09:00:00Z',
            headRefName: 'feat/open-c',
            baseRefName: 'main',
          },
        ]),
      },
    );

    expect(report.summary.remoteMergedCandidates).toBe(1);
    expect(report.summary.remoteStaleCandidates).toBe(4);
    expect(report.summary.staleByRiskBand).toEqual({ low: 2, standard: 0, high: 2 });
    expect(report.summary.staleByPrState).toEqual({
      open: 1,
      closed: 1,
      merged: 0,
      none: 1,
      ambiguous: 1,
      unavailable: 0,
    });
    expect(report.remoteMerged[0]).toEqual(
      expect.objectContaining({
        branch: 'docs/merged-a',
        prState: 'merged',
        deleteCommand: "git push 'origin' --delete 'docs/merged-a'",
      }),
    );
    expect(report.remoteStale).toEqual([
      expect.objectContaining({ branch: 'docs/stale-a', prState: 'closed', riskBand: 'low', proposedAction: 'delete-review' }),
      expect.objectContaining({ branch: 'feat/stale-b', prState: 'ambiguous', riskBand: 'high', proposedAction: 'manual-review' }),
      expect.objectContaining({ branch: 'feat/open-c', prState: 'open', riskBand: 'high', proposedAction: 'keep-review' }),
      expect.objectContaining({ branch: 'ci/stale-d', prState: 'none', riskBand: 'low', proposedAction: 'delete-review' }),
    ]);
    expect(report.templates.issueComment).toContain('Remote branch triage summary');
    expect(report.sourceInventory.path).toBe('tmp/maintenance/branch-inventory.json');
  });

  it('writes markdown and json outputs with gh lookup disabled', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-branch-triage-'));
    const inputJson = join(sandbox, 'branch-inventory.json');
    const outputJson = join(sandbox, 'remote-branch-triage.json');
    const outputMd = join(sandbox, 'remote-branch-triage.md');

    try {
      mkdirSync(sandbox, { recursive: true });
      writeFileSync(
        inputJson,
        `${JSON.stringify(
          {
            generatedAt: '2026-03-06T10:00:00Z',
            base: 'origin/main',
            remote: 'origin',
            candidates: {
              remoteMerged: ['feat/merged-a'],
              remoteStaleByAge: [{ branch: 'feat/stale-a', ageDays: 120 }],
            },
          },
          null,
          2,
        )}\n`,
        'utf8',
      );

      const result = spawnSync(
        'node',
        [
          triageScript,
          '--input-json',
          inputJson,
          '--output-json',
          outputJson,
          '--output-md',
          outputMd,
          '--gh-pr-limit',
          '0',
        ],
        {
          cwd: repoRoot,
          encoding: 'utf8',
          timeout: 120_000,
        },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);

      const report = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(report.summary.remoteMergedCandidates).toBe(1);
      expect(report.summary.remoteStaleCandidates).toBe(1);
      expect(report.githubPullRequests).toEqual(
        expect.objectContaining({
          available: false,
          disabled: true,
          requestedLimit: 0,
        }),
      );

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toContain('GitHub PR lookup: disabled');
      expect(markdown).toContain('Remote delete commands (operator approval required)');
      expect(markdown).toContain("git push 'origin' --delete 'feat/merged-a'");
      expect(markdown).toContain('Issue/comment template');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('escapes markdown table meta characters in rendered cells', async () => {
    const mod = await import(triageModuleUrl);
    const markdown = mod.renderMarkdown({
      generatedAt: '2026-03-06T11:00:00Z',
      sourceInventory: {
        path: 'tmp/maintenance/branch-inventory.json',
        generatedAt: '2026-03-06T10:00:00Z',
        base: 'origin/main',
        remote: 'origin',
      },
      githubPullRequests: {
        available: true,
        disabled: false,
        reason: '',
        requestedBaseBranch: 'main',
        requestedLimit: 1000,
        matchedItems: 2,
      },
      summary: {
        remoteMergedCandidates: 1,
        remoteStaleCandidates: 1,
        staleByRiskBand: { low: 1, standard: 0, high: 0 },
        staleByPrState: { open: 0, closed: 1, merged: 0, none: 0, ambiguous: 0, unavailable: 0 },
        topPrefixes: [{ prefix: 'docs', count: 1, examples: ['docs\\unsafe|branch'] }],
      },
      remoteMerged: [
        {
          branch: 'feat\\unsafe|name',
          proposedAction: 'delete',
          approval: 'required',
          prState: 'merged',
          baseBranches: ['main'],
          deleteCommand: "git push 'origin' --delete 'feat\\unsafe|name'",
          latestPr: { number: 2466, state: 'merged' },
        },
      ],
      remoteStale: [
        {
          branch: 'docs\\stale|branch',
          ageDays: 120,
          riskBand: 'low',
          prState: 'closed',
          latestPr: { number: 2401, state: 'closed' },
          baseBranches: ['main'],
          proposedAction: 'delete-review',
          decision: 'keep',
          notes: 'line1\\check|value\nline2',
        },
      ],
      templates: {
        issueComment: 'line1\\value|x\nline2',
      },
    });

    expect(markdown).toContain('feat\\\\unsafe\\|name');
    expect(markdown).toContain('docs\\\\stale\\|branch');
    expect(markdown).toContain('#2466 (merged)');
    expect(markdown).toContain('#2401 (closed)');
    expect(markdown).toContain('line1\\\\check\\|value<br>line2');
    expect(markdown).toContain('line1\\value|x');
  });
});
