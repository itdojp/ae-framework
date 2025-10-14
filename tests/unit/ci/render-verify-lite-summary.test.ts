import { describe, expect, it } from 'vitest';
import { renderVerifyLiteSummary } from '../../../scripts/ci/lib/verify-lite-summary.mjs';

describe('renderVerifyLiteSummary', () => {
  const baseSummary = {
    schemaVersion: '1.0.0',
    timestamp: '2025-10-06T00:00:00Z',
    flags: {
      install: '--frozen-lockfile',
      noFrozen: false,
      keepLintLog: true,
      enforceLint: false,
      runMutation: true
    },
    steps: {
      install: { status: 'success', notes: 'flags=--frozen-lockfile', retried: false },
      lint: { status: 'failure', notes: '2618 violations' },
      build: { status: 'success' },
      bddLint: { status: 'skipped' },
      mutationQuick: { status: 'success', notes: 'score: 59.74%' },
      conformanceReport: { status: 'success', notes: 'runs=1;violations=0' }
    },
    artifacts: {
      lintSummary: 'verify-lite-lint-summary.json',
      lintLog: 'verify-lite-lint.log',
      mutationSummary: 'reports/mutation/summary.json',
      mutationSurvivors: 'reports/mutation/survivors.json',
      conformanceSummary: 'reports/conformance/verify-lite-summary.json',
      conformanceSummaryMarkdown: 'reports/conformance/verify-lite-summary.md'
    }
  };

  it('renders markdown summary with schema version and flags', () => {
    const result = renderVerifyLiteSummary(baseSummary, { artifactsUrl: 'https://example.com/artifacts' });
    expect(result).toMatchSnapshot();
  });

  it('handles missing optional notes and artifacts', () => {
    const minimal = {
      schemaVersion: '1.0.0',
      timestamp: '2025-10-06T01:23:45Z',
      flags: {
        install: '',
        noFrozen: true,
        keepLintLog: false,
        enforceLint: false,
        runMutation: false
      },
      steps: {
        typeCheck: { status: 'success' },
        lint: { status: 'skipped' }
      },
      artifacts: {
        lintSummary: null,
        lintLog: null,
        mutationSummary: null,
        mutationSurvivors: null,
        conformanceSummary: null,
        conformanceSummaryMarkdown: null
      }
    };

    const result = renderVerifyLiteSummary(minimal);
    expect(result).toMatchSnapshot();
  });

  it('escapes HTML-sensitive characters in notes', () => {
    const summary = {
      ...baseSummary,
      steps: {
        ...baseSummary.steps,
        lint: { status: 'failure', notes: '<script>alert("xss")</script>' }
      }
    };

    const result = renderVerifyLiteSummary(summary);
    expect(result).toContain('&lt;script&gt;alert(&quot;xss&quot;)&lt;/script&gt;');
  });

  it('throws on invalid payload', () => {
    // @ts-expect-error deliberate bad input
    expect(() => renderVerifyLiteSummary(null)).toThrowErrorMatchingInlineSnapshot(
      "[Error: Invalid summary payload]"
    );
  });
});
