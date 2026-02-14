import { describe, expect, it } from 'vitest';
import {
  buildConsecutiveFailureStats,
  buildMttrStats,
  buildSloStats,
  buildSummaryMarkdown,
  classifyIncidentType,
  extractAutomationReportsFromLog,
  formatTopReasonTable,
  joinCountMap,
  parseCsv,
  parseEventTimestamp,
  resolveIncidentScope,
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
        generatedAt: '2026-02-13T00:10:00.000Z',
        run: { url: 'https://example/runs/1' },
      },
      {
        schemaVersion: 'ae-automation-report/v1',
        tool: 'auto-merge-enabler',
        status: 'blocked',
        reason: 'checks pending',
        generatedAt: '2026-02-13T00:20:00.000Z',
        run: { url: 'https://example/runs/2' },
      },
      {
        schemaVersion: 'ae-automation-report/v1',
        tool: 'auto-merge-enabler',
        status: 'resolved',
        reason: 'completed',
        generatedAt: '2026-02-13T00:50:00.000Z',
        run: { url: 'https://example/runs/3' },
      },
      {
        schemaVersion: 'ae-automation-report/v1',
        tool: 'copilot-auto-fix',
        status: 'error',
        reason: 'api timeout',
        generatedAt: '2026-02-13T01:00:00.000Z',
        run: { url: 'https://example/runs/4' },
      },
      {
        schemaVersion: 'ae-automation-report/v1',
        tool: 'copilot-auto-fix',
        status: 'resolved',
        reason: 'completed',
        generatedAt: '2026-02-13T02:00:00.000Z',
        run: { url: 'https://example/runs/4' },
      },
    ];

    const summary = summarizeAutomationReports(reports, {
      topN: 2,
      sloTargetPercent: 60,
      mttrTargetMinutes: 70,
    });
    expect(summary.totalReports).toBe(5);
    expect(summary.totalFailures).toBe(2);
    expect(summary.byStatus.resolved).toBe(3);
    expect(summary.byStatus.blocked).toBe(1);
    expect(summary.byTool['auto-merge-enabler']).toBe(2);
    expect(summary.topFailureReasons).toHaveLength(2);
    const reasonMap = new Map(summary.topFailureReasons.map((item) => [item.reason, item]));
    expect(reasonMap.get('checks pending')?.count).toBe(1);
    expect(reasonMap.get('checks pending')?.sampleRuns).toContain('https://example/runs/2');
    expect(reasonMap.get('api timeout')?.count).toBe(1);
    expect(summary.maxConsecutiveFailures).toBe(1);
    expect(summary.maxConsecutiveFailuresByTool['auto-merge-enabler']).toBe(1);
    expect(summary.slo.successRatePercent).toBe(60);
    expect(summary.slo.achieved).toBe(true);
    expect(summary.mttr.recoveries).toBe(2);
    expect(summary.mttr.meanMinutes).toBe(45);
    expect(summary.mttr.achieved).toBe(true);
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

  it('extracts timestamps and classifies incident types', () => {
    const report = {
      status: 'blocked',
      reason: 'behind base branch',
      generatedAt: '2026-02-13T00:00:00.000Z',
    };
    expect(parseEventTimestamp(report)).toBe(Date.parse('2026-02-13T00:00:00.000Z'));
    expect(classifyIncidentType(report)).toBe('behind_loop');
    expect(resolveIncidentScope({ prNumber: 42 })).toBe('pr:42');
    expect(resolveIncidentScope({ run: { ref: 'refs/pull/51/merge' } })).toBe('pr:51');
    expect(classifyIncidentType({ status: 'error', reason: 'HTTP 429 Too Many Requests' })).toBe('rate_limit_429');
  });

  it('calculates consecutive failure stats by tool', () => {
    const stats = buildConsecutiveFailureStats(
      [
        { tool: 'a', status: 'blocked', generatedAt: '2026-02-13T00:00:00.000Z' },
        { tool: 'a', status: 'error', generatedAt: '2026-02-13T00:01:00.000Z' },
        { tool: 'a', status: 'resolved', generatedAt: '2026-02-13T00:02:00.000Z' },
        { tool: 'b', status: 'error', generatedAt: '2026-02-13T00:03:00.000Z' },
      ],
      { failureStatuses: ['error', 'blocked'] },
    );

    expect(stats.maxConsecutiveFailures).toBe(2);
    expect(stats.maxConsecutiveFailuresByTool.a).toBe(2);
    expect(stats.maxConsecutiveFailuresByTool.b).toBe(1);
  });

  it('builds SLO and MTTR stats from reports', () => {
    const reports = [
      {
        status: 'blocked',
        reason: 'behind base',
        tool: 'auto-merge-enabler',
        generatedAt: '2026-02-13T00:00:00.000Z',
        run: { url: 'https://example/runs/11' },
      },
      {
        status: 'resolved',
        reason: 'completed',
        tool: 'auto-merge-enabler',
        generatedAt: '2026-02-13T00:30:00.000Z',
        run: { url: 'https://example/runs/12' },
      },
      {
        status: 'error',
        reason: 'HTTP 429 Too Many Requests',
        tool: 'copilot-auto-fix',
        generatedAt: '2026-02-13T01:00:00.000Z',
        run: { url: 'https://example/runs/13' },
      },
      {
        status: 'resolved',
        reason: 'completed',
        tool: 'copilot-auto-fix',
        generatedAt: '2026-02-13T01:45:00.000Z',
        run: { url: 'https://example/runs/14' },
      },
      {
        status: 'blocked',
        reason: 'merge conflict',
        tool: 'pr-self-heal',
        generatedAt: '2026-02-13T02:00:00.000Z',
        run: { url: 'https://example/runs/15' },
      },
    ];

    const slo = buildSloStats({
      totalReports: 5,
      totalFailures: 3,
      targetPercent: 70,
    });
    expect(slo.successRatePercent).toBe(40);
    expect(slo.achieved).toBe(false);

    const mttr = buildMttrStats(reports, {
      failureStatuses: ['error', 'blocked'],
      targetMinutes: 50,
    });
    expect(mttr.recoveries).toBe(2);
    expect(mttr.meanMinutes).toBe(37.5);
    expect(mttr.p95Minutes).toBe(45);
    expect(mttr.unresolvedOpenIncidents).toBe(1);
    expect(mttr.achieved).toBe(true);
    expect(mttr.byIncidentType.some((item) => item.incidentType === 'rate_limit_429')).toBe(true);
    expect(mttr.byIncidentType.some((item) => item.incidentType === 'behind_loop')).toBe(true);
    expect(mttr.byIncidentType.some((item) => item.incidentType === 'blocked')).toBe(true);
  });

  it('matches overlapping incidents by tool and scope', () => {
    const reports = [
      {
        status: 'blocked',
        reason: 'checks pending',
        tool: 'auto-merge-enabler',
        prNumber: 101,
        generatedAt: '2026-02-13T00:00:00.000Z',
      },
      {
        status: 'blocked',
        reason: 'checks pending',
        tool: 'auto-merge-enabler',
        prNumber: 102,
        generatedAt: '2026-02-13T00:05:00.000Z',
      },
      {
        status: 'resolved',
        reason: 'completed',
        tool: 'auto-merge-enabler',
        prNumber: 101,
        generatedAt: '2026-02-13T00:20:00.000Z',
      },
      {
        status: 'resolved',
        reason: 'completed',
        tool: 'auto-merge-enabler',
        prNumber: 102,
        generatedAt: '2026-02-13T00:35:00.000Z',
      },
    ];

    const mttr = buildMttrStats(reports, {
      failureStatuses: ['error', 'blocked'],
      targetMinutes: 30,
    });

    expect(mttr.recoveries).toBe(2);
    expect(mttr.unresolvedOpenIncidents).toBe(0);
    expect(mttr.meanMinutes).toBe(25);
    expect(mttr.p95Minutes).toBe(30);
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
        maxConsecutiveFailures: 1,
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
        slo: {
          targetPercent: 95,
          successRatePercent: 66.67,
          achieved: false,
        },
        mttr: {
          targetMinutes: 120,
          meanMinutes: 90,
          p95Minutes: 130,
          unresolvedOpenIncidents: 1,
          achieved: true,
          byIncidentType: [
            {
              incidentType: 'review_gate',
              recoveries: 2,
              meanMinutes: 90,
              p95Minutes: 130,
              unresolvedOpenIncidents: 1,
              samples: ['https://example/runs/123'],
            },
          ],
        },
      },
      outputPath: '/tmp/out.json',
    });
    expect(lines[0]).toBe('## Automation Observability Weekly Summary');
    expect(lines.some((line) => line.includes('failures(error/blocked): 1'))).toBe(true);
    expect(lines.some((line) => line.includes('maxConsecutiveFailures: 1'))).toBe(true);
    expect(lines.some((line) => line.includes('SLO successRate'))).toBe(true);
    expect(lines.some((line) => line.includes('MTTR mean'))).toBe(true);
    expect(lines.some((line) => line.includes('MTTR by incident type'))).toBe(true);
    expect(lines.some((line) => line.includes('Top failure reasons'))).toBe(true);
  });
});
