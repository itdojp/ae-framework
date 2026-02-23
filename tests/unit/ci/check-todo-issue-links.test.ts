import { describe, expect, it, vi } from 'vitest';
import {
  buildIssueReferenceMap,
  evaluateIssueReferenceMap,
  fetchIssueStates,
  parseTodoIssueReferences,
} from '../../../scripts/ci/check-todo-issue-links.mjs';

describe('check-todo-issue-links', () => {
  it('parses TODO/FIXME issue references with source location', () => {
    const content = [
      '// TODO(#123): implement',
      '/* FIXME(#456) pending */',
      '// TODO ( #789 ) spacing variant',
    ].join('\n');

    const references = parseTodoIssueReferences(content, 'src/sample.ts');
    expect(references).toEqual([
      expect.objectContaining({ file: 'src/sample.ts', line: 1, column: 4, marker: 'TODO', issue: 123 }),
      expect.objectContaining({ file: 'src/sample.ts', line: 2, column: 4, marker: 'FIXME', issue: 456 }),
      expect.objectContaining({ file: 'src/sample.ts', line: 3, column: 4, marker: 'TODO', issue: 789 }),
    ]);
  });

  it('detects closed and missing issue references and respects allow list', () => {
    const references = [
      { file: 'src/a.ts', line: 10, column: 3, marker: 'TODO', issue: 10 },
      { file: 'src/b.ts', line: 20, column: 3, marker: 'TODO', issue: 20 },
      { file: 'src/c.ts', line: 30, column: 3, marker: 'FIXME', issue: 30 },
    ];
    const referenceMap = buildIssueReferenceMap(references);
    const issueStates = new Map([
      [10, { state: 'open' as const }],
      [20, { state: 'closed' as const }],
      [30, { state: 'missing' as const }],
    ]);

    const evaluation = evaluateIssueReferenceMap(referenceMap, issueStates, { allowIssues: [30] });
    expect(evaluation.closed).toHaveLength(1);
    expect(evaluation.closed[0]?.issue).toBe(20);
    expect(evaluation.missing).toHaveLength(0);
    expect(evaluation.unresolved).toHaveLength(0);
    expect(evaluation.violations).toHaveLength(1);
  });

  it('fetches issue states via GitHub API responses', async () => {
    const fetchImpl = vi.fn(async (url: string) => {
      if (url.endsWith('/issues/1')) {
        return {
          ok: true,
          status: 200,
          json: async () => ({ state: 'open', html_url: 'https://example.test/issues/1' }),
          text: async () => '',
        };
      }
      if (url.endsWith('/issues/2')) {
        return {
          ok: true,
          status: 200,
          json: async () => ({ state: 'closed', html_url: 'https://example.test/issues/2' }),
          text: async () => '',
        };
      }
      return {
        ok: false,
        status: 404,
        json: async () => ({}),
        text: async () => 'not found',
      };
    });

    const states = await fetchIssueStates([1, 2, 3], {
      repository: 'itdojp/ae-framework',
      token: '',
      fetchImpl: fetchImpl as unknown as typeof fetch,
    });

    expect(states.get(1)).toEqual({ state: 'open', url: 'https://example.test/issues/1' });
    expect(states.get(2)).toEqual({ state: 'closed', url: 'https://example.test/issues/2' });
    expect(states.get(3)).toEqual({
      state: 'missing',
      url: 'https://api.github.com/repos/itdojp/ae-framework/issues/3',
    });
    expect(fetchImpl).toHaveBeenCalledTimes(3);
  });
});
