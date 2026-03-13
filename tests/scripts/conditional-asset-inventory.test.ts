import { describe, expect, it } from 'vitest';
import {
  buildConditionalAssetAudit,
  classifyConditionalOrigin,
  renderMarkdownReport,
  resolveGeneratedAt,
} from '../../scripts/legal/inventory-conditional-assets.mjs';

describe('conditional asset audit', () => {
  it('classifies conditional paths by origin class', () => {
    expect(classifyConditionalOrigin('fixtures/agents/sample.ae-handoff.json')).toBe('test-fixture');
    expect(classifyConditionalOrigin('test-cassettes/Custom_directory_test.json')).toBe('test-cassette');
    expect(classifyConditionalOrigin('artifacts/reference/types/public-types.current.d.ts')).toBe(
      'tracked-reference-snapshot',
    );
    expect(classifyConditionalOrigin('artifacts/archive/2025/example.md')).toBe('tracked-archive');
    expect(classifyConditionalOrigin('artifacts/plan/plan-artifact.json')).toBe('committed-contract-artifact');
    expect(classifyConditionalOrigin('artifacts/tmp/untracked-output.json')).toBe(
      'runtime-output-or-unclassified',
    );
  });

  it('builds summary counts and nested notice inventory', () => {
    const audit = buildConditionalAssetAudit({
      trackedFiles: [
        'fixtures/agents/sample.ae-handoff.json',
        'test-cassettes/Custom_directory_test.json',
        'artifacts/reference/types/public-types.current.d.ts',
        'artifacts/archive/2025/example.md',
        'artifacts/plan/plan-artifact.json',
        'artifacts/reference/legal/LICENSE-THIRD-PARTY.txt',
      ],
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.generatedAt).toBe('2026-03-13T00:00:00.000Z');
    expect(audit.gitHeadSha).toBe('1111111111111111111111111111111111111111');
    expect(audit.summary.total).toBe(6);
    expect(audit.summary.byScope).toEqual({
      artifacts: 4,
      fixtures: 1,
      'test-cassettes': 1,
    });
    expect(audit.summary.byOriginClass['tracked-reference-snapshot']).toBe(2);
    expect(audit.summary.nestedNoticeFiles).toBe(1);
    expect(audit.nestedNoticeFiles).toEqual(['artifacts/reference/legal/LICENSE-THIRD-PARTY.txt']);
  });

  it('renders markdown report', () => {
    const markdown = renderMarkdownReport({
      generatedAt: '2026-03-13T00:00:00.000Z',
      gitHeadSha: '1111111111111111111111111111111111111111',
      summary: {
        total: 2,
        byScope: { artifacts: 1, fixtures: 1, 'test-cassettes': 0 },
        byOriginClass: {
          'tracked-reference-snapshot': 1,
          'test-fixture': 1,
        },
        nestedNoticeFiles: 0,
      },
      nestedNoticeFiles: [],
      items: [
        {
          path: 'artifacts/reference/types/public-types.current.d.ts',
          scope: 'artifacts',
          originClass: 'tracked-reference-snapshot',
          nestedNotice: false,
        },
        {
          path: 'fixtures/agents/sample.ae-handoff.json',
          scope: 'fixtures',
          originClass: 'test-fixture',
          nestedNotice: false,
        },
      ],
    });

    expect(markdown).toContain('# Conditional Asset Provenance Audit');
    expect(markdown).toContain('- gitHeadSha: 1111111111111111111111111111111111111111');
    expect(markdown).toContain('- artifacts: 1');
    expect(markdown).toContain('- tracked-reference-snapshot: 1');
    expect(markdown).toContain('`fixtures/agents/sample.ae-handoff.json`');
  });

  it('escapes markdown table cells in rendered items', () => {
    const markdown = renderMarkdownReport({
      generatedAt: '2026-03-13T00:00:00.000Z',
      gitHeadSha: '1111111111111111111111111111111111111111',
      summary: {
        total: 1,
        byScope: { artifacts: 1, fixtures: 0, 'test-cassettes': 0 },
        byOriginClass: { 'runtime-output-or-unclassified': 1 },
        nestedNoticeFiles: 0,
      },
      nestedNoticeFiles: [],
      items: [
        {
          path: 'artifacts/tmp/a|b`c.json',
          scope: 'artifacts',
          originClass: 'runtime-output-or-unclassified',
          nestedNotice: false,
        },
      ],
    });

    expect(markdown).toContain('`artifacts/tmp/a\\|b\\`c.json`');
  });

  it('resolves generatedAt from SOURCE_DATE_EPOCH seconds', () => {
    expect(resolveGeneratedAt('0')).toBe('1970-01-01T00:00:00.000Z');
  });

  it('rejects invalid SOURCE_DATE_EPOCH values', () => {
    expect(() => resolveGeneratedAt('not-a-number')).toThrow(
      'SOURCE_DATE_EPOCH must be an integer number of seconds',
    );
  });

  it('always emits all scope keys and rejects missing gitHeadSha', () => {
    expect(
      buildConditionalAssetAudit({
        trackedFiles: ['fixtures/agents/sample.ae-handoff.json'],
        gitHeadSha: '1111111111111111111111111111111111111111',
        generatedAt: '2026-03-13T00:00:00.000Z',
      }).summary.byScope,
    ).toEqual({
      artifacts: 0,
      fixtures: 1,
      'test-cassettes': 0,
    });

    expect(() =>
      buildConditionalAssetAudit({
        trackedFiles: [],
        generatedAt: '2026-03-13T00:00:00.000Z',
      }),
    ).toThrow('gitHeadSha is required');
  });
});
