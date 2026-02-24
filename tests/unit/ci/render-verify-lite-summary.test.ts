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
      contextPackValidation: { status: 'success', notes: 'validated spec/context-pack' },
      contextPackFunctorValidation: { status: 'success', notes: 'validated context-pack functor mapping' },
      contextPackNaturalTransformationValidation: {
        status: 'success',
        notes: 'validated context-pack natural transformation mapping'
      },
      contextPackProductCoproductValidation: {
        status: 'success',
        notes: 'validated context-pack product/coproduct mapping;uncovered_variants=0'
      },
      contextPackPhase5Validation: {
        status: 'success',
        notes: 'validated context-pack phase5 templates;violations=0'
      },
      bddLint: { status: 'skipped' },
      mutationQuick: { status: 'success', notes: 'score: 59.74%' },
      conformanceReport: { status: 'success', notes: 'runs=1;violations=0' }
    },
    traceability: {
      status: 'success',
      missingCount: 2,
      matrixPath: 'docs/specs/ISSUE-TRACEABILITY-MATRIX.json',
      notes: 'matrix=docs/specs/ISSUE-TRACEABILITY-MATRIX.json;missing=2'
    },
    artifacts: {
      lintSummary: 'artifacts/verify-lite/verify-lite-lint-summary.json',
      lintLog: 'artifacts/verify-lite/verify-lite-lint.log',
      mutationSummary: 'reports/mutation/summary.json',
      mutationSurvivors: 'reports/mutation/survivors.json',
      contextPackReportJson: 'artifacts/context-pack/context-pack-validate-report.json',
      contextPackReportMarkdown: 'artifacts/context-pack/context-pack-validate-report.md',
      contextPackFunctorReportJson: 'artifacts/context-pack/context-pack-functor-report.json',
      contextPackFunctorReportMarkdown: 'artifacts/context-pack/context-pack-functor-report.md',
      contextPackNaturalTransformationReportJson:
        'artifacts/context-pack/context-pack-natural-transformation-report.json',
      contextPackNaturalTransformationReportMarkdown:
        'artifacts/context-pack/context-pack-natural-transformation-report.md',
      contextPackProductCoproductReportJson:
        'artifacts/context-pack/context-pack-product-coproduct-report.json',
      contextPackProductCoproductReportMarkdown:
        'artifacts/context-pack/context-pack-product-coproduct-report.md',
      contextPackPhase5ReportJson: 'artifacts/context-pack/context-pack-phase5-report.json',
      contextPackPhase5ReportMarkdown: 'artifacts/context-pack/context-pack-phase5-report.md',
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
      traceability: {
        status: 'skipped',
        missingCount: 0,
        matrixPath: null,
        notes: 'matrix_not_found'
      },
      artifacts: {
        lintSummary: null,
        lintLog: null,
        mutationSummary: null,
        mutationSurvivors: null,
        contextPackReportJson: null,
        contextPackReportMarkdown: null,
        contextPackFunctorReportJson: null,
        contextPackFunctorReportMarkdown: null,
        contextPackNaturalTransformationReportJson: null,
        contextPackNaturalTransformationReportMarkdown: null,
        contextPackProductCoproductReportJson: null,
        contextPackProductCoproductReportMarkdown: null,
        contextPackPhase5ReportJson: null,
        contextPackPhase5ReportMarkdown: null,
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
