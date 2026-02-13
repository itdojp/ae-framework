import { describe, expect, it } from 'vitest';
import {
  extractAutomationReportsFromLog,
  summarizeAutomationReports,
} from '../../../scripts/ci/automation-observability-weekly.mjs';

describe('automation-observability-weekly', () => {
  it('extracts automation reports from mixed logs', () => {
    const log = [
      'plain line',
      '[ae-automation-report] {"schemaVersion":"ae-automation-report/v1","tool":"pr-self-heal","status":"resolved","reason":"completed"}',
      'gate\tCheck\t2026-02-13T00:00:00Z [ae-automation-report] {"schemaVersion":"ae-automation-report/v1","tool":"auto-merge-enabler","status":"blocked","reason":"checks pending"}',
      '[ae-automation-report] not-json',
      '[ae-automation-report] {"schemaVersion":"other","tool":"x","status":"error"}',
    ].join('\n');

    const reports = extractAutomationReportsFromLog(log);
    expect(reports).toHaveLength(2);
    expect(reports[0].tool).toBe('pr-self-heal');
    expect(reports[1].status).toBe('blocked');
  });

  it('summarizes statuses, tools, and top failure reasons', () => {
    const reports = [
      {
        schemaVersion: 'ae-automation-report/v1',
        tool: 'pr-self-heal',
        status: 'resolved',
        reason: 'completed',
        run: { url: 'https://example/runs/1' },
      },
      {
        schemaVersion: 'ae-automation-report/v1',
        tool: 'auto-merge-enabler',
        status: 'blocked',
        reason: 'checks pending',
        run: { url: 'https://example/runs/2' },
      },
      {
        schemaVersion: 'ae-automation-report/v1',
        tool: 'auto-merge-enabler',
        status: 'blocked',
        reason: 'checks pending',
        run: { url: 'https://example/runs/3' },
      },
      {
        schemaVersion: 'ae-automation-report/v1',
        tool: 'copilot-auto-fix',
        status: 'error',
        reason: 'api timeout',
        run: { url: 'https://example/runs/4' },
      },
    ];

    const summary = summarizeAutomationReports(reports, { topN: 2 });
    expect(summary.totalReports).toBe(4);
    expect(summary.totalFailures).toBe(3);
    expect(summary.byStatus.resolved).toBe(1);
    expect(summary.byStatus.blocked).toBe(2);
    expect(summary.byTool['auto-merge-enabler']).toBe(2);
    expect(summary.topFailureReasons).toHaveLength(2);
    expect(summary.topFailureReasons[0].reason).toBe('checks pending');
    expect(summary.topFailureReasons[0].count).toBe(2);
    expect(summary.topFailureReasons[0].sampleRuns).toContain('https://example/runs/2');
    expect(summary.topFailureReasons[1].reason).toBe('api timeout');
  });
});
