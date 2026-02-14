import { describe, expect, it } from 'vitest';
import {
  ALERT_MARKER,
  buildAlertCommentBody,
  canPostIssueComment,
  buildConsecutiveFailureStats,
  buildFingerprint,
  evaluateAlertConditions,
  listIssueComments,
  findSuppressionState,
  normalizeAlertChannel,
  parseFingerprint,
  shouldEvaluateSuppression,
} from '../../../scripts/ci/automation-observability-alert.mjs';

describe('automation-observability-alert', () => {
  it('builds consecutive failure stats from ordered events', () => {
    const stats = buildConsecutiveFailureStats([
      { tool: 'a', status: 'blocked', generatedAt: '2026-02-14T00:00:00.000Z' },
      { tool: 'a', status: 'error', generatedAt: '2026-02-14T00:01:00.000Z' },
      { tool: 'a', status: 'resolved', generatedAt: '2026-02-14T00:02:00.000Z' },
      { tool: 'b', status: 'error', generatedAt: '2026-02-14T00:03:00.000Z' },
    ]);
    expect(stats.maxConsecutiveFailures).toBe(2);
    expect(stats.maxConsecutiveFailuresByTool.a).toBe(2);
    expect(stats.maxConsecutiveFailuresByTool.b).toBe(1);
  });

  it('evaluates blocked/consecutive/slo/mttr alert conditions', () => {
    const payload = {
      config: { sinceIso: '2026-02-07T00:00:00.000Z' },
      summary: {
        totalReports: 10,
        totalFailures: 5,
        byStatus: { blocked: 4, resolved: 5, error: 1 },
        maxConsecutiveFailures: 4,
        topFailureReasons: [{ reason: 'checks pending', count: 3, sampleRuns: ['https://example/runs/1'] }],
        slo: { successRatePercent: 50, targetPercent: 95 },
        mttr: { meanMinutes: 180, targetMinutes: 120 },
      },
    };

    const result = evaluateAlertConditions(payload, {
      maxBlocked: 2,
      maxConsecutiveFailures: 3,
    });
    const codes = result.alerts.map((item) => item.code);
    expect(codes).toContain('blocked_spike');
    expect(codes).toContain('consecutive_failures');
    expect(codes).toContain('slo_breach');
    expect(codes).toContain('mttr_breach');
  });

  it('builds deterministic fingerprint', () => {
    const fingerprintA = buildFingerprint({
      repository: 'itdojp/ae-framework',
      sinceIso: '2026-02-07T00:00:00.000Z',
      alerts: [{ code: 'blocked_spike', value: 4, threshold: 2 }],
    });
    const fingerprintB = buildFingerprint({
      repository: 'itdojp/ae-framework',
      sinceIso: '2026-02-07T00:00:00.000Z',
      alerts: [{ code: 'blocked_spike', value: 4, threshold: 2 }],
    });
    expect(fingerprintA).toHaveLength(16);
    expect(fingerprintA).toBe(fingerprintB);
  });

  it('suppresses duplicate fingerprint and cooldown violations', () => {
    const nowMs = Date.parse('2026-02-14T12:00:00.000Z');
    const duplicate = findSuppressionState(
      [
        {
          id: 1,
          created_at: '2026-02-14T11:00:00.000Z',
          body: `${ALERT_MARKER}\n<!-- AE-AUTOMATION-ALERT-FP deadbeefdeadbeef -->`,
        },
      ],
      {
        fingerprint: 'deadbeefdeadbeef',
        cooldownHours: 24,
        nowMs,
      }
    );
    expect(duplicate.suppressed).toBe(true);
    expect(duplicate.reason).toBe('duplicate_fingerprint');

    const cooldown = findSuppressionState(
      [
        {
          id: 2,
          created_at: '2026-02-14T10:00:00.000Z',
          body: `${ALERT_MARKER}\n<!-- AE-AUTOMATION-ALERT-FP cafebabecafebabe -->`,
        },
      ],
      {
        fingerprint: '1111222233334444',
        cooldownHours: 4,
        nowMs,
      }
    );
    expect(cooldown.suppressed).toBe(true);
    expect(cooldown.reason).toBe('cooldown_active');
  });

  it('paginates issue comments for suppression checks', () => {
    const pages = {
      1: Array.from({ length: 2 }, (_, index) => ({ id: index + 1 })),
      2: Array.from({ length: 2 }, (_, index) => ({ id: index + 3 })),
      3: [{ id: 5 }],
    };
    const calls = [];
    const comments = listIssueComments('itdojp/ae-framework', 1963, {
      perPage: 2,
      fetchPage: (_repo, _issue, page) => {
        calls.push(page);
        return pages[page] || [];
      },
    });

    expect(calls).toEqual([1, 2, 3]);
    expect(comments.map((item) => item.id)).toEqual([1, 2, 3, 4, 5]);
  });

  it('normalizes channel and posting decision', () => {
    expect(normalizeAlertChannel('issue_comment')).toBe('issue_comment');
    expect(normalizeAlertChannel('dry_run')).toBe('dry_run');
    expect(normalizeAlertChannel('invalid-channel')).toBe('dry_run');
    expect(
      shouldEvaluateSuppression({
        alerts: [{ code: 'blocked_spike' }],
        issueNumber: 1963,
      })
    ).toBe(true);
    expect(canPostIssueComment({ channel: 'issue_comment', dryRun: false, suppressed: false })).toBe(true);
    expect(canPostIssueComment({ channel: 'dry_run', dryRun: true, suppressed: false })).toBe(false);
  });

  it('renders alert comment body with marker and fingerprint', () => {
    const body = buildAlertCommentBody({
      repository: 'itdojp/ae-framework',
      issueNumber: 1963,
      payload: { config: { sinceIso: '2026-02-07T00:00:00.000Z' } },
      summary: {
        totalReports: 10,
        totalFailures: 4,
        byStatus: { blocked: 3 },
        maxConsecutiveFailures: 4,
        topFailureReasons: [{ reason: 'checks pending', count: 2, sampleRuns: ['https://example/runs/2'] }],
      },
      alerts: [{ code: 'blocked_spike', severity: 'high', value: 3, threshold: 2 }],
      fingerprint: 'feedfacefeedface',
    });

    expect(body).toContain(ALERT_MARKER);
    expect(body).toContain('Automation Observability Alert');
    expect(body).toContain('blocked_spike');
    expect(parseFingerprint(body)).toBe('feedfacefeedface');
  });
});
