#!/usr/bin/env node

import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execGh, execGhJson } from './lib/gh-exec.mjs';

const ALERT_MARKER = '<!-- AE-AUTOMATION-ALERT v1 -->';
const ALERT_FINGERPRINT_PREFIX = '<!-- AE-AUTOMATION-ALERT-FP ';
const DEFAULT_FAILURE_STATUSES = ['error', 'blocked'];
const DEFAULT_MAX_BLOCKED = 2;
const DEFAULT_MAX_CONSECUTIVE_FAILURES = 3;
const DEFAULT_COOLDOWN_HOURS = 24;
const DEFAULT_OUTPUT_PATH = 'artifacts/automation/weekly-alert-summary.json';
const DEFAULT_INPUT_PATH = 'artifacts/automation/weekly-failure-summary.json';
const DEFAULT_CHANNEL = 'issue_comment';
const DEFAULT_COMMENTS_PER_PAGE = 100;
const DEFAULT_MAX_COMMENT_PAGES = 100;

function toInt(value, fallback, min = 0) {
  const raw = String(value ?? '').trim();
  if (!raw) return fallback;
  const numeric = Number(raw);
  if (!Number.isFinite(numeric)) return fallback;
  const parsed = Math.trunc(numeric);
  if (parsed < min) return fallback;
  return parsed;
}

function toBool(value, fallback = false) {
  const raw = String(value ?? '').trim().toLowerCase();
  if (!raw) return fallback;
  return ['1', 'true', 'yes', 'on'].includes(raw);
}

function parseEventTimestamp(report) {
  const candidates = [
    report?.generatedAt,
    report?.run?.createdAt,
    report?.__meta?.runCreatedAt,
  ];
  for (const candidate of candidates) {
    const raw = String(candidate || '').trim();
    if (!raw) continue;
    const parsed = Date.parse(raw);
    if (Number.isFinite(parsed)) return parsed;
  }
  return null;
}

function buildConsecutiveFailureStats(reports, failureStatuses = DEFAULT_FAILURE_STATUSES) {
  const failureSet = new Set(Array.isArray(failureStatuses) ? failureStatuses : DEFAULT_FAILURE_STATUSES);
  const events = (Array.isArray(reports) ? reports : [])
    .map((report, index) => ({
      index,
      tool: String(report?.tool || 'unknown').trim() || 'unknown',
      status: String(report?.status || 'unknown').trim().toLowerCase(),
      timestampMs: parseEventTimestamp(report),
    }))
    .sort((a, b) => {
      if (Number.isFinite(a.timestampMs) && Number.isFinite(b.timestampMs)) {
        return a.timestampMs - b.timestampMs || a.index - b.index;
      }
      if (Number.isFinite(a.timestampMs)) return -1;
      if (Number.isFinite(b.timestampMs)) return 1;
      return a.index - b.index;
    });

  const currentByTool = new Map();
  const maxByTool = {};
  let maxConsecutiveFailures = 0;

  for (const event of events) {
    const previous = currentByTool.get(event.tool) || 0;
    if (failureSet.has(event.status)) {
      const next = previous + 1;
      currentByTool.set(event.tool, next);
      maxByTool[event.tool] = Math.max(maxByTool[event.tool] || 0, next);
      maxConsecutiveFailures = Math.max(maxConsecutiveFailures, next);
      continue;
    }
    currentByTool.set(event.tool, 0);
  }

  return {
    maxConsecutiveFailures,
    maxConsecutiveFailuresByTool: maxByTool,
  };
}

function round2(value) {
  if (!Number.isFinite(value)) return null;
  return Math.round(value * 100) / 100;
}

function numberOrNull(value) {
  if (value === null || value === undefined) return null;
  const numeric = Number(value);
  return Number.isFinite(numeric) ? numeric : null;
}

function normalizeSummary(payload = {}) {
  const summary = payload.summary && typeof payload.summary === 'object'
    ? { ...payload.summary }
    : {};
  if (!Number.isFinite(numberOrNull(summary.maxConsecutiveFailures))) {
    const reports = Array.isArray(payload.reports) ? payload.reports : [];
    const stats = buildConsecutiveFailureStats(reports);
    summary.maxConsecutiveFailures = stats.maxConsecutiveFailures;
    summary.maxConsecutiveFailuresByTool = stats.maxConsecutiveFailuresByTool;
  }
  if (!summary.byStatus || typeof summary.byStatus !== 'object') {
    summary.byStatus = {};
  }
  if (!Array.isArray(summary.topFailureReasons)) {
    summary.topFailureReasons = [];
  }
  return summary;
}

function evaluateAlertConditions(payload, options = {}) {
  const summary = normalizeSummary(payload);
  const alerts = [];
  const maxBlocked = toInt(options.maxBlocked, DEFAULT_MAX_BLOCKED, 0);
  const maxConsecutiveFailures = toInt(
    options.maxConsecutiveFailures,
    DEFAULT_MAX_CONSECUTIVE_FAILURES,
    1,
  );

  const blocked = toInt(summary.byStatus?.blocked, 0, 0);
  if (blocked > maxBlocked) {
    alerts.push({
      code: 'blocked_spike',
      severity: 'high',
      value: blocked,
      threshold: maxBlocked,
      message: `blocked count ${blocked} exceeds threshold ${maxBlocked}`,
    });
  }

  const consecutive = toInt(summary.maxConsecutiveFailures, 0, 0);
  if (consecutive > maxConsecutiveFailures) {
    alerts.push({
      code: 'consecutive_failures',
      severity: 'high',
      value: consecutive,
      threshold: maxConsecutiveFailures,
      message: `max consecutive failures ${consecutive} exceeds threshold ${maxConsecutiveFailures}`,
    });
  }

  const sloSuccessRate = numberOrNull(summary.slo?.successRatePercent);
  const sloTarget = numberOrNull(options.sloTargetPercent ?? summary.slo?.targetPercent);
  if (sloSuccessRate !== null && sloTarget !== null && sloSuccessRate < sloTarget) {
    alerts.push({
      code: 'slo_breach',
      severity: 'high',
      value: round2(sloSuccessRate),
      threshold: round2(sloTarget),
      message: `SLO success rate ${round2(sloSuccessRate)}% is below target ${round2(sloTarget)}%`,
    });
  }

  const mttrMean = numberOrNull(summary.mttr?.meanMinutes);
  const mttrTarget = numberOrNull(options.mttrTargetMinutes ?? summary.mttr?.targetMinutes);
  if (mttrMean !== null && mttrTarget !== null && mttrMean > mttrTarget) {
    alerts.push({
      code: 'mttr_breach',
      severity: 'high',
      value: round2(mttrMean),
      threshold: round2(mttrTarget),
      message: `MTTR mean ${round2(mttrMean)} min exceeds target ${round2(mttrTarget)} min`,
    });
  }

  return { summary, alerts };
}

function buildFingerprint({ repository, sinceIso, alerts }) {
  const normalized = {
    repository,
    sinceIso,
    alerts: (alerts || []).map((alert) => ({
      code: alert.code,
      value: alert.value,
      threshold: alert.threshold,
    })),
  };
  return crypto
    .createHash('sha256')
    .update(JSON.stringify(normalized))
    .digest('hex')
    .slice(0, 16);
}

function buildActionHints(alerts) {
  const actions = [];
  const codes = new Set((alerts || []).map((item) => item.code));
  if (codes.has('blocked_spike')) {
    actions.push('`status:blocked` PR の理由を確認し、`pr-self-heal` 再実行または手動更新を実施');
  }
  if (codes.has('consecutive_failures')) {
    actions.push('連続失敗した workflow の最新 run logs を確認し、同一要因の再発を遮断');
  }
  if (codes.has('slo_breach')) {
    actions.push('Top failure reasons の上位要因を修正し、次週の成功率改善を確認');
  }
  if (codes.has('mttr_breach')) {
    actions.push('復旧導線を `docs/ci/automation-rollback-runbook.md` で再確認し、手動介入時間を短縮');
  }
  return actions.length > 0 ? actions : ['現時点で追加対応は不要'];
}

function pickSampleRunUrl(summary) {
  const firstReason = Array.isArray(summary?.topFailureReasons) ? summary.topFailureReasons[0] : null;
  const sampleRuns = Array.isArray(firstReason?.sampleRuns) ? firstReason.sampleRuns : [];
  return sampleRuns[0] || '';
}

function buildAlertCommentBody({
  repository,
  issueNumber,
  payload,
  summary,
  alerts,
  fingerprint,
}) {
  const sinceIso = String(payload?.config?.sinceIso || payload?.generatedAt || '').trim() || '-';
  const topReason = summary.topFailureReasons?.[0];
  const sampleRun = pickSampleRunUrl(summary);
  const actionHints = buildActionHints(alerts);

  const lines = [
    ALERT_MARKER,
    '## Automation Observability Alert',
    `- generatedAt: ${new Date().toISOString()}`,
    `- repository: ${repository}`,
    `- issue: #${issueNumber}`,
    `- since: ${sinceIso}`,
    `- totalReports: ${summary.totalReports ?? '-'}`,
    `- totalFailures: ${summary.totalFailures ?? '-'}`,
    `- blocked: ${summary.byStatus?.blocked ?? 0}`,
    `- maxConsecutiveFailures: ${summary.maxConsecutiveFailures ?? 0}`,
    '',
    '### Triggered conditions',
    '| Code | Severity | Value | Threshold |',
    '| --- | --- | ---: | ---: |',
    ...alerts.map((alert) => `| ${alert.code} | ${alert.severity} | ${alert.value} | ${alert.threshold ?? '-'} |`),
    '',
    '### Cause (initial)',
    `- topFailureReason: ${topReason ? `${topReason.reason} (${topReason.count})` : '-'}`,
    '',
    '### Impact',
    '- PR 自動化の停止/遅延が増加し、レビュー完了からマージまでのリードタイムが延伸する可能性があります。',
    '',
    '### Primary actions',
    ...actionHints.map((line) => `- ${line}`),
    '',
    '### References',
    `- sampleRun: ${sampleRun || '-'}`,
    '- docs: `docs/ci/automation-observability.md`',
    '- runbook: `docs/ci/automation-rollback-runbook.md`',
    `${ALERT_FINGERPRINT_PREFIX}${fingerprint} -->`,
  ];
  return lines.join('\n');
}

function readJsonFile(filePath) {
  const resolved = path.resolve(filePath);
  const raw = fs.readFileSync(resolved, 'utf8');
  return JSON.parse(raw);
}

function writeJsonFile(filePath, payload) {
  const resolved = path.resolve(filePath);
  const dir = path.dirname(resolved);
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
  fs.writeFileSync(resolved, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
  return resolved;
}

function appendStepSummary(lines, env = process.env) {
  const summaryPath = String(env.GITHUB_STEP_SUMMARY || '').trim();
  if (!summaryPath) return;
  const dir = path.dirname(summaryPath);
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
  fs.appendFileSync(summaryPath, `${lines.join('\n')}\n`, 'utf8');
}

function parseFingerprint(body) {
  const text = String(body || '');
  const match = text.match(/<!-- AE-AUTOMATION-ALERT-FP ([a-f0-9]{16}) -->/u);
  return match ? match[1] : null;
}

function fetchIssueCommentsPage(repository, issueNumber, page, perPage = DEFAULT_COMMENTS_PER_PAGE) {
  return execGhJson([
    'api',
    `repos/${repository}/issues/${issueNumber}/comments?per_page=${perPage}&page=${page}`,
  ]);
}

function listIssueComments(repository, issueNumber, options = {}) {
  const perPage = toInt(options.perPage, DEFAULT_COMMENTS_PER_PAGE, 1);
  const maxPages = toInt(options.maxPages, DEFAULT_MAX_COMMENT_PAGES, 1);
  const fetchPage = typeof options.fetchPage === 'function'
    ? options.fetchPage
    : fetchIssueCommentsPage;

  const comments = [];
  for (let page = 1; page <= maxPages; page += 1) {
    const pageComments = fetchPage(repository, issueNumber, page, perPage);
    if (!Array.isArray(pageComments) || pageComments.length === 0) {
      break;
    }
    comments.push(...pageComments);
    if (pageComments.length < perPage) {
      break;
    }
  }
  return comments;
}

function normalizeAlertChannel(value) {
  const raw = String(value || '').trim().toLowerCase();
  if (raw === 'issue_comment') return 'issue_comment';
  if (raw === 'dry_run') return 'dry_run';
  if (!raw) return DEFAULT_CHANNEL;
  return 'dry_run';
}

function shouldEvaluateSuppression({ alerts, issueNumber }) {
  return Array.isArray(alerts) && alerts.length > 0 && Number.isFinite(issueNumber) && issueNumber > 0;
}

function canPostIssueComment({ channel, dryRun, suppressed }) {
  return channel === 'issue_comment' && !dryRun && !suppressed;
}

function findSuppressionState(comments, { fingerprint, cooldownHours, nowMs }) {
  const markerComments = (Array.isArray(comments) ? comments : [])
    .filter((comment) => typeof comment?.body === 'string' && comment.body.includes(ALERT_MARKER))
    .map((comment) => ({
      id: comment.id,
      createdAtMs: Date.parse(String(comment.created_at || '')),
      fingerprint: parseFingerprint(comment.body),
    }))
    .filter((item) => Number.isFinite(item.createdAtMs))
    .sort((a, b) => b.createdAtMs - a.createdAtMs);

  const hasSameFingerprint = markerComments.some((item) => item.fingerprint === fingerprint);
  if (hasSameFingerprint) {
    return { suppressed: true, reason: 'duplicate_fingerprint' };
  }

  if (cooldownHours <= 0 || markerComments.length === 0) {
    return { suppressed: false, reason: null };
  }

  const latest = markerComments[0];
  const elapsedMs = nowMs - latest.createdAtMs;
  if (elapsedMs < cooldownHours * 60 * 60 * 1000) {
    return { suppressed: true, reason: 'cooldown_active' };
  }
  return { suppressed: false, reason: null };
}

function postIssueComment(repository, issueNumber, body) {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'ae-automation-alert-'));
  const bodyPath = path.join(tmpDir, 'comment.md');
  fs.writeFileSync(bodyPath, body, 'utf8');
  try {
    execGh([
      'issue',
      'comment',
      String(issueNumber),
      '--repo',
      repository,
      '--body-file',
      bodyPath,
    ]);
  } finally {
    try {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    } catch {
      // Cleanup failure is non-fatal.
    }
  }
}

function buildStepSummaryLines(result) {
  const lines = [
    '## Automation Observability Alerts',
    `- generatedAt: ${result.generatedAt}`,
    `- repository: ${result.repository}`,
    `- channel: ${result.channel}`,
    `- alerts: ${result.alerts.length}`,
    `- posted: ${result.posted}`,
    `- suppressed: ${result.suppressed}`,
  ];
  if (result.suppressedReason) {
    lines.push(`- suppressedReason: ${result.suppressedReason}`);
  }
  if (result.alerts.length > 0) {
    lines.push('');
    lines.push('### Triggered');
    for (const alert of result.alerts) {
      lines.push(`- ${alert.code}: ${alert.message}`);
    }
  }
  return lines;
}

function main(env = process.env) {
  const repository = String(env.AE_AUTOMATION_REPOSITORY || env.GITHUB_REPOSITORY || '').trim();
  if (!repository) {
    throw new Error('AE_AUTOMATION_REPOSITORY or GITHUB_REPOSITORY is required');
  }

  const inputPath = String(
    env.AE_AUTOMATION_OBSERVABILITY_ALERT_INPUT || DEFAULT_INPUT_PATH
  ).trim();
  const outputPath = String(
    env.AE_AUTOMATION_OBSERVABILITY_ALERT_OUTPUT || DEFAULT_OUTPUT_PATH
  ).trim();
  const issueNumber = toInt(env.AE_AUTOMATION_ALERT_ISSUE_NUMBER, 0, 1);
  const channel = normalizeAlertChannel(env.AE_AUTOMATION_ALERT_CHANNEL || DEFAULT_CHANNEL);
  const dryRun = toBool(env.AE_AUTOMATION_ALERT_DRY_RUN, false) || channel === 'dry_run';
  const cooldownHours = toInt(env.AE_AUTOMATION_ALERT_COOLDOWN_HOURS, DEFAULT_COOLDOWN_HOURS, 0);

  const payload = readJsonFile(inputPath);
  const evaluated = evaluateAlertConditions(payload, {
    maxBlocked: env.AE_AUTOMATION_ALERT_MAX_BLOCKED,
    maxConsecutiveFailures: env.AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES,
    sloTargetPercent: env.AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT,
    mttrTargetMinutes: env.AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES,
  });
  const summary = evaluated.summary;
  const alerts = evaluated.alerts;
  const fingerprint = buildFingerprint({
    repository,
    sinceIso: payload?.config?.sinceIso || payload?.generatedAt || '',
    alerts,
  });

  let posted = false;
  let suppressed = false;
  let suppressedReason = null;

  if (shouldEvaluateSuppression({ alerts, issueNumber })) {
    const comments = listIssueComments(repository, issueNumber);
    const suppression = findSuppressionState(comments, {
      fingerprint,
      cooldownHours,
      nowMs: Date.now(),
    });
    suppressed = suppression.suppressed;
    suppressedReason = suppression.reason;

    if (canPostIssueComment({ channel, dryRun, suppressed })) {
      const body = buildAlertCommentBody({
        repository,
        issueNumber,
        payload,
        summary,
        alerts,
        fingerprint,
      });
      postIssueComment(repository, issueNumber, body);
      posted = true;
    }
  }

  const result = {
    generatedAt: new Date().toISOString(),
    repository,
    channel,
    issueNumber: issueNumber || null,
    inputPath: path.resolve(inputPath),
    alerts,
    suppressed,
    suppressedReason,
    posted,
    dryRun,
    fingerprint,
    summary: {
      totalReports: summary.totalReports ?? 0,
      totalFailures: summary.totalFailures ?? 0,
      blocked: toInt(summary.byStatus?.blocked, 0, 0),
      maxConsecutiveFailures: toInt(summary.maxConsecutiveFailures, 0, 0),
      slo: summary.slo ?? null,
      mttr: summary.mttr ?? null,
    },
  };

  const resolvedOutputPath = writeJsonFile(outputPath, result);
  appendStepSummary(buildStepSummaryLines(result), env);

  console.log(`[automation-observability-alert] wrote ${resolvedOutputPath}`);
  console.log(
    `[automation-observability-alert] alerts=${alerts.length} posted=${posted} suppressed=${suppressed}`
  );
  return result;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}

export {
  ALERT_FINGERPRINT_PREFIX,
  ALERT_MARKER,
  buildAlertCommentBody,
  buildConsecutiveFailureStats,
  buildFingerprint,
  buildStepSummaryLines,
  canPostIssueComment,
  evaluateAlertConditions,
  fetchIssueCommentsPage,
  findSuppressionState,
  listIssueComments,
  main,
  normalizeAlertChannel,
  parseEventTimestamp,
  parseFingerprint,
  shouldEvaluateSuppression,
  toBool,
  toInt,
};
