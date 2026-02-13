import { describe, expect, it } from 'vitest';
import {
  buildSummaryMarkdown,
  extractAutomationReportsFromLog,
  formatTopReasonTable,
  joinCountMap,
  parseCsv,
  summarizeAutomationReports,
  toInt,
  toIsoCutoff,
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

  it('parses integers with min validation', () => {
    expect(toInt('12', 7, 0)).toBe(12);
    expect(toInt('12.9', 7, 0)).toBe(12);
    expect(toInt('1', 7, 3)).toBe(7);
    expect(toInt('x', 7, 0)).toBe(7);
    expect(toInt('', 7, 0)).toBe(7);
  });

  it('parses CSV values and trims spaces', () => {
    expect(parseCsv('')).toEqual([]);
    expect(parseCsv('PR Self-Heal')).toEqual(['PR Self-Heal']);
    expect(parseCsv('A, B , ,C')).toEqual(['A', 'B', 'C']);
  });

  it('returns ISO cutoff string around expected range', () => {
    const now = Date.now();
    const cutoff = Date.parse(toIsoCutoff(2));
    const expected = now - (2 * 24 * 60 * 60 * 1000);
    expect(Number.isFinite(cutoff)).toBe(true);
    expect(Math.abs(cutoff - expected)).toBeLessThan(10_000);
  });

  it('formats count maps and top reason tables', () => {
    expect(joinCountMap({})).toBe('-');
    expect(joinCountMap({ blocked: 2, error: 3 })).toBe('error:3, blocked:2');
    expect(formatTopReasonTable({ topFailureReasons: [] })).toEqual([
      'No failure reasons were observed in this period.',
    ]);
    const table = formatTopReasonTable({
      topFailureReasons: [
        {
          reason: 'checks pending',
          count: 2,
          statuses: { blocked: 2 },
          tools: { 'auto-merge-enabler': 2 },
          sampleRuns: ['https://example/runs/2'],
        },
      ],
    });
    expect(table[0]).toContain('| Rank | Reason |');
    expect(table[2]).toContain('checks pending');
  });

  it('builds markdown summary with key sections', () => {
    const lines = buildSummaryMarkdown({
      repo: 'itdojp/ae-framework',
      sinceIso: '2026-02-01T00:00:00.000Z',
      workflows: ['PR Self-Heal', 'PR Maintenance'],
      runStats: {
        listedRuns: 4,
        scannedRuns: 3,
        logsFailed: 0,
        workflows: {},
      },
      summary: {
        totalReports: 3,
        totalFailures: 1,
        byStatus: { resolved: 2, blocked: 1 },
        byTool: { 'pr-self-heal': 2, 'auto-merge-enabler': 1 },
        topFailureReasons: [
          {
            reason: 'checks pending',
            count: 1,
            statuses: { blocked: 1 },
            tools: { 'auto-merge-enabler': 1 },
            sampleRuns: ['https://example/runs/123'],
          },
        ],
      },
      outputPath: '/tmp/out.json',
    });
    expect(lines[0]).toBe('## Automation Observability Weekly Summary');
    expect(lines.some((line) => line.includes('failures(error/blocked): 1'))).toBe(true);
    expect(lines.some((line) => line.includes('Top failure reasons'))).toBe(true);
  });
});
