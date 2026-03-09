import { describe, expect, it } from 'vitest';

import {
  buildUiE2ESummary,
  renderMarkdown,
  toAdapterSummary,
} from '../../../scripts/e2e/run-ui-e2e-semantic.mjs';

describe('run-ui-e2e-semantic helpers', () => {
  it('builds an ok summary for fully passing scenarios', () => {
    const summary = buildUiE2ESummary({
      baseUrl: 'http://127.0.0.1:3100',
      ariaDir: 'artifacts/e2e/ui-aria-snapshots',
      generatedAt: '2026-03-09T12:30:00.000Z',
      scenarios: [
        {
          id: 'health-overview',
          title: 'Health page exposes operational status',
          status: 'pass',
          startedAt: '2026-03-09T12:30:00.000Z',
          finishedAt: '2026-03-09T12:30:01.000Z',
          durationMs: 1000,
          url: 'http://127.0.0.1:3100/ja/health',
          semanticChecks: ['heading visible'],
          diagnostics: [],
          ariaSnapshotPath: 'artifacts/e2e/ui-aria-snapshots/health-overview-success.txt',
        },
      ],
    });

    expect(summary.status).toBe('ok');
    expect(summary.summary.passed).toBe(1);
    expect(summary.summary.failed).toBe(0);
    expect(summary.artifacts.ariaSnapshotsDir).toBe('artifacts/e2e/ui-aria-snapshots');
  });

  it('builds an error summary and adapter summary for failed scenarios', () => {
    const summary = buildUiE2ESummary({
      baseUrl: 'http://127.0.0.1:3100',
      ariaDir: 'artifacts/e2e/ui-aria-snapshots',
      adapterSummaryPath: 'artifacts/custom/ui-summary.json',
      generatedAt: '2026-03-09T12:30:00.000Z',
      scenarios: [
        {
          id: 'semantic-form',
          title: 'Semantic form validates and submits accessibly',
          status: 'fail',
          startedAt: '2026-03-09T12:30:00.000Z',
          finishedAt: '2026-03-09T12:30:01.000Z',
          durationMs: 1000,
          url: 'http://127.0.0.1:3100/ja/e2e/semantic-form',
          semanticChecks: ['form submit'],
          diagnostics: [
            {
              kind: 'semantic',
              message: 'Timed out waiting for role=alert',
              ariaSnapshotPath: 'artifacts/e2e/ui-aria-snapshots/semantic-form-failure.txt',
            },
          ],
          ariaSnapshotPath: 'artifacts/e2e/ui-aria-snapshots/semantic-form-failure.txt',
        },
      ],
    });

    const adapterSummary = toAdapterSummary(summary, 'artifacts/e2e/summary.json');
    const markdown = renderMarkdown(summary);

    expect(summary.status).toBe('error');
    expect(summary.artifacts.adapterSummaryPath).toBe('artifacts/custom/ui-summary.json');
    expect(adapterSummary.adapter).toBe('ui-e2e');
    expect(adapterSummary.status).toBe('error');
    expect(adapterSummary.details[0]?.diagnostics[0]).toContain('Timed out waiting');
    expect(markdown).toContain('## Diagnostics');
    expect(markdown).toContain('semantic-form');
  });
});
