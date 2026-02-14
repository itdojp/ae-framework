#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import { execGh, execGhJson } from './lib/gh-exec.mjs';

const REPORT_PREFIX = '[ae-automation-report] ';
const REPORT_SCHEMA = 'ae-automation-report/v1';
const DEFAULT_WORKFLOWS = [
  'PR Self-Heal',
  'Codex Autopilot Lane',
  'PR Maintenance',
  'Copilot Auto Fix',
];
const DEFAULT_FAILURE_STATUSES = ['error', 'blocked'];
const DEFAULT_SLO_TARGET_PERCENT = 95;
const DEFAULT_MTTR_TARGET_MINUTES = 120;

function toInt(value, fallback, min = 0) {
  const raw = String(value ?? '').trim();
  if (!raw) return fallback;
  const numeric = Number(raw);
  if (!Number.isFinite(numeric)) {
    return fallback;
  }
  const parsed = Math.trunc(numeric);
  if (parsed < min) return fallback;
  return parsed;
}

function parseCsv(value) {
  return String(value || '')
    .split(',')
    .map((item) => item.trim())
    .filter(Boolean);
}

function toIsoCutoff(days) {
  return new Date(Date.now() - (days * 24 * 60 * 60 * 1000)).toISOString();
}

function extractAutomationReportsFromLog(logText, prefix = REPORT_PREFIX) {
  const lines = String(logText || '').split(/\r?\n/u);
  const reports = [];
  for (const line of lines) {
    const idx = line.indexOf(prefix);
    if (idx < 0) continue;
    const payload = line.slice(idx + prefix.length).trim();
    if (!payload.startsWith('{')) continue;
    try {
      const parsed = JSON.parse(payload);
      if (parsed && parsed.schemaVersion === REPORT_SCHEMA) {
        reports.push(parsed);
      }
    } catch {
      // Ignore malformed payload lines and continue parsing.
    }
  }
  return reports;
}

function joinCountMap(mapObj) {
  const entries = Object.entries(mapObj || {});
  if (entries.length === 0) return '-';
  return entries
    .sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]))
    .map(([key, count]) => `${key}:${count}`)
    .join(', ');
}

function parseEventTimestamp(report) {
  const candidates = [
    report?.generatedAt,
    report?.run?.createdAt,
    report?.__meta?.runCreatedAt,
  ];
  for (const value of candidates) {
    const raw = String(value || '').trim();
    if (!raw) continue;
    const parsed = Date.parse(raw);
    if (Number.isFinite(parsed)) {
      return parsed;
    }
  }
  return null;
}

function classifyIncidentType(report) {
  const status = String(report?.status || '').trim().toLowerCase();
  const reason = String(report?.reason || '').trim().toLowerCase();

  if (reason.includes('429') || reason.includes('too many requests') || reason.includes('rate limit')) {
    return 'rate_limit_429';
  }
  if (reason.includes('behind')) {
    return 'behind_loop';
  }
  if (reason.includes('gate') || reason.includes('review')) {
    return 'review_gate';
  }
  if (status === 'blocked' || reason.includes('blocked') || reason.includes('conflict')) {
    return 'blocked';
  }
  return 'other';
}

function percentile(values, ratio) {
  if (!Array.isArray(values) || values.length === 0) return null;
  const sorted = [...values].sort((a, b) => a - b);
  const index = Math.max(0, Math.min(sorted.length - 1, Math.ceil(sorted.length * ratio) - 1));
  return sorted[index];
}

function round2(value) {
  if (!Number.isFinite(value)) return null;
  return Math.round(value * 100) / 100;
}

function buildSloStats({ totalReports, totalFailures, targetPercent }) {
  const successful = Math.max(0, totalReports - totalFailures);
  const successRatePercent = totalReports > 0
    ? round2((successful / totalReports) * 100)
    : null;
  return {
    targetPercent,
    successfulReports: successful,
    totalReports,
    successRatePercent,
    achieved: successRatePercent !== null ? successRatePercent >= targetPercent : null,
  };
}

function buildMttrStats(reports, { failureStatuses, targetMinutes }) {
  const failureSet = new Set(Array.isArray(failureStatuses) ? failureStatuses : []);
  const events = (Array.isArray(reports) ? reports : [])
    .map((report) => ({
      report,
      tool: String(report?.tool || 'unknown').trim() || 'unknown',
      status: String(report?.status || 'unknown').trim() || 'unknown',
      timestampMs: parseEventTimestamp(report),
      reason: String(report?.reason || '').trim(),
      runUrl: String(report?.run?.url || '').trim(),
      incidentType: classifyIncidentType(report),
    }))
    .filter((item) => Number.isFinite(item.timestampMs))
    .sort((a, b) => a.timestampMs - b.timestampMs);

  const openByTool = new Map();
  const durationsMs = [];
  const byIncidentType = new Map();

  const ensureTypeBucket = (incidentType) => {
    if (!byIncidentType.has(incidentType)) {
      byIncidentType.set(incidentType, {
        incidentType,
        recoveries: 0,
        unresolvedOpenIncidents: 0,
        meanMinutes: null,
        p95Minutes: null,
        samples: [],
        _durationsMs: [],
      });
    }
    return byIncidentType.get(incidentType);
  };

  for (const event of events) {
    const isFailure = failureSet.has(event.status);
    if (isFailure) {
      if (!openByTool.has(event.tool)) {
        const bucket = ensureTypeBucket(event.incidentType);
        if (event.runUrl && bucket.samples.length < 3) {
          bucket.samples.push(event.runUrl);
        }
        openByTool.set(event.tool, {
          startedAtMs: event.timestampMs,
          incidentType: event.incidentType,
        });
      }
      continue;
    }

    if (event.status !== 'resolved') {
      continue;
    }

    if (!openByTool.has(event.tool)) {
      continue;
    }

    const openIncident = openByTool.get(event.tool);
    const duration = Math.max(0, event.timestampMs - openIncident.startedAtMs);
    durationsMs.push(duration);
    const bucket = ensureTypeBucket(openIncident.incidentType);
    bucket.recoveries += 1;
    bucket._durationsMs.push(duration);
    if (event.runUrl && bucket.samples.length < 3) {
      bucket.samples.push(event.runUrl);
    }
    openByTool.delete(event.tool);
  }

  for (const incident of openByTool.values()) {
    const bucket = ensureTypeBucket(incident.incidentType);
    bucket.unresolvedOpenIncidents += 1;
  }

  const byIncidentTypeSummary = [...byIncidentType.values()]
    .map((item) => {
      const meanMs = item._durationsMs.length > 0
        ? item._durationsMs.reduce((sum, value) => sum + value, 0) / item._durationsMs.length
        : null;
      const p95Ms = percentile(item._durationsMs, 0.95);
      return {
        incidentType: item.incidentType,
        recoveries: item.recoveries,
        unresolvedOpenIncidents: item.unresolvedOpenIncidents,
        meanMinutes: meanMs === null ? null : round2(meanMs / 60000),
        p95Minutes: p95Ms === null ? null : round2(p95Ms / 60000),
        samples: item.samples,
      };
    })
    .sort((a, b) => {
      const recoveriesDiff = b.recoveries - a.recoveries;
      if (recoveriesDiff !== 0) return recoveriesDiff;
      return a.incidentType.localeCompare(b.incidentType);
    });

  const meanMs = durationsMs.length > 0
    ? durationsMs.reduce((sum, value) => sum + value, 0) / durationsMs.length
    : null;
  const p95Ms = percentile(durationsMs, 0.95);
  const unresolvedOpenIncidents = openByTool.size;
  const meanMinutes = meanMs === null ? null : round2(meanMs / 60000);
  const p95Minutes = p95Ms === null ? null : round2(p95Ms / 60000);

  return {
    targetMinutes,
    recoveries: durationsMs.length,
    unresolvedOpenIncidents,
    meanMinutes,
    p95Minutes,
    achieved: meanMinutes !== null ? meanMinutes <= targetMinutes : null,
    byIncidentType: byIncidentTypeSummary,
  };
}

function summarizeAutomationReports(reports, options = {}) {
  const topN = toInt(options.topN, 5, 1);
  const sloTargetPercent = Math.min(100, Math.max(0, toInt(
    options.sloTargetPercent,
    DEFAULT_SLO_TARGET_PERCENT,
    0,
  )));
  const mttrTargetMinutes = toInt(options.mttrTargetMinutes, DEFAULT_MTTR_TARGET_MINUTES, 1);
  const failureStatuses = new Set(
    Array.isArray(options.failureStatuses) && options.failureStatuses.length > 0
      ? options.failureStatuses
      : DEFAULT_FAILURE_STATUSES,
  );

  const byStatus = {};
  const byTool = {};
  const reasonMap = new Map();
  let failures = 0;

  for (const report of reports) {
    const status = String(report.status || 'unknown').trim() || 'unknown';
    const tool = String(report.tool || 'unknown').trim() || 'unknown';
    byStatus[status] = (byStatus[status] || 0) + 1;
    byTool[tool] = (byTool[tool] || 0) + 1;

    if (!failureStatuses.has(status)) {
      continue;
    }

    failures += 1;
    const reason = String(report.reason || '').trim() || '(no reason)';
    if (!reasonMap.has(reason)) {
      reasonMap.set(reason, {
        reason,
        count: 0,
        statuses: {},
        tools: {},
        sampleRuns: [],
      });
    }
    const entry = reasonMap.get(reason);
    entry.count += 1;
    entry.statuses[status] = (entry.statuses[status] || 0) + 1;
    entry.tools[tool] = (entry.tools[tool] || 0) + 1;

    const runUrl = String(report.run?.url || '').trim();
    if (runUrl && !entry.sampleRuns.includes(runUrl) && entry.sampleRuns.length < 3) {
      entry.sampleRuns.push(runUrl);
    }
  }

  const topFailureReasons = [...reasonMap.values()]
    .sort((a, b) => b.count - a.count || a.reason.localeCompare(b.reason))
    .slice(0, topN)
    .map((item) => ({
      reason: item.reason,
      count: item.count,
      statuses: item.statuses,
      tools: item.tools,
      sampleRuns: item.sampleRuns,
    }));

  return {
    totalReports: reports.length,
    totalFailures: failures,
    byStatus,
    byTool,
    topFailureReasons,
    slo: buildSloStats({
      totalReports: reports.length,
      totalFailures: failures,
      targetPercent: sloTargetPercent,
    }),
    mttr: buildMttrStats(reports, {
      failureStatuses: [...failureStatuses],
      targetMinutes: mttrTargetMinutes,
    }),
  };
}

function escapeMarkdownCell(value) {
  return String(value || '').replace(/\|/gu, '\\|').replace(/\n/gu, ' ');
}

function formatTopReasonTable(summary) {
  if (!summary.topFailureReasons || summary.topFailureReasons.length === 0) {
    return ['No failure reasons were observed in this period.'];
  }

  const lines = [
    '| Rank | Reason | Count | Status | Tool | Sample run |',
    '| ---: | --- | ---: | --- | --- | --- |',
  ];
  summary.topFailureReasons.forEach((item, index) => {
    const sampleRun = item.sampleRuns && item.sampleRuns.length > 0
      ? item.sampleRuns[0]
      : '-';
    lines.push(
      `| ${index + 1} | ${escapeMarkdownCell(item.reason)} | ${item.count} | ${escapeMarkdownCell(joinCountMap(item.statuses))} | ${escapeMarkdownCell(joinCountMap(item.tools))} | ${escapeMarkdownCell(sampleRun)} |`,
    );
  });
  return lines;
}

function appendStepSummary(lines, env = process.env) {
  const target = String(env.GITHUB_STEP_SUMMARY || '').trim();
  if (!target) return;
  const dir = path.dirname(target);
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
  fs.appendFileSync(target, `${lines.join('\n')}\n`, 'utf8');
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

function listRuns(repo, workflow, limit) {
  return execGhJson([
    'run', 'list',
    '--repo', repo,
    '--workflow', workflow,
    '--limit', String(limit),
    '--json', 'databaseId,createdAt,status,conclusion,event,displayTitle,url',
  ]);
}

function fetchRunLog(repo, runId) {
  return execGh([
    'run', 'view',
    String(runId),
    '--repo', repo,
    '--log',
  ]);
}

function collectReportsFromRuns(repo, workflows, sinceIso, maxRunsPerWorkflow) {
  const reports = [];
  const warnings = [];
  const runStats = {
    listedRuns: 0,
    scannedRuns: 0,
    logsFailed: 0,
    workflows: {},
  };

  for (const workflow of workflows) {
    const runs = listRuns(repo, workflow, maxRunsPerWorkflow);
    runStats.listedRuns += runs.length;
    runStats.workflows[workflow] = {
      listed: runs.length,
      scanned: 0,
      reports: 0,
      logErrors: 0,
    };

    const candidates = runs.filter((run) => {
      const createdAt = String(run.createdAt || '').trim();
      return createdAt && createdAt >= sinceIso;
    });

    for (const run of candidates) {
      runStats.scannedRuns += 1;
      runStats.workflows[workflow].scanned += 1;
      try {
        const logText = fetchRunLog(repo, run.databaseId);
        const extracted = extractAutomationReportsFromLog(logText);
        for (const report of extracted) {
          reports.push({
            ...report,
            run: {
              ...(report.run && typeof report.run === 'object' ? report.run : {}),
              url: report.run?.url || run.url,
            },
            __meta: {
              workflow,
              runId: run.databaseId,
              runCreatedAt: run.createdAt,
              runConclusion: run.conclusion || '',
            },
          });
        }
        runStats.workflows[workflow].reports += extracted.length;
      } catch (error) {
        runStats.logsFailed += 1;
        runStats.workflows[workflow].logErrors += 1;
        warnings.push({
          workflow,
          runId: run.databaseId,
          message: error && error.message ? error.message : String(error),
        });
      }
    }
  }

  return { reports, warnings, runStats };
}

function buildSummaryMarkdown({ repo, sinceIso, workflows, runStats, summary, outputPath }) {
  const lines = [
    '## Automation Observability Weekly Summary',
    `- generatedAt: ${new Date().toISOString()}`,
    `- repository: ${repo}`,
    `- since: ${sinceIso}`,
    `- workflows: ${workflows.join(', ')}`,
    `- listedRuns: ${runStats.listedRuns}`,
    `- scannedRuns: ${runStats.scannedRuns}`,
    `- reports: ${summary.totalReports}`,
    `- failures(error/blocked): ${summary.totalFailures}`,
    `- SLO successRate: ${summary.slo?.successRatePercent ?? 'n/a'}% (target: ${summary.slo?.targetPercent ?? 'n/a'}%, achieved: ${summary.slo?.achieved === null ? 'n/a' : summary.slo.achieved})`,
    `- MTTR mean: ${summary.mttr?.meanMinutes ?? 'n/a'} min (target: ${summary.mttr?.targetMinutes ?? 'n/a'} min, achieved: ${summary.mttr?.achieved === null ? 'n/a' : summary.mttr.achieved})`,
    `- MTTR p95: ${summary.mttr?.p95Minutes ?? 'n/a'} min, unresolvedOpenIncidents: ${summary.mttr?.unresolvedOpenIncidents ?? 'n/a'}`,
    `- output: ${outputPath}`,
    '',
    '### Status breakdown',
    `- ${joinCountMap(summary.byStatus)}`,
    '',
    '### Tool breakdown',
    `- ${joinCountMap(summary.byTool)}`,
    '',
    '### Top failure reasons',
    ...formatTopReasonTable(summary),
    '',
    '### MTTR by incident type',
    ...(summary.mttr?.byIncidentType?.length
      ? [
        '| Incident Type | Recoveries | Mean (min) | P95 (min) | Unresolved | Sample run |',
        '| --- | ---: | ---: | ---: | ---: | --- |',
        ...summary.mttr.byIncidentType.map((item) => (
          `| ${escapeMarkdownCell(item.incidentType)} | ${item.recoveries} | ${item.meanMinutes ?? '-'} | ${item.p95Minutes ?? '-'} | ${item.unresolvedOpenIncidents} | ${escapeMarkdownCell(item.samples?.[0] || '-')} |`
        )),
      ]
      : ['No MTTR incident buckets were observed in this period.']),
  ];
  return lines;
}

function main(env = process.env) {
  const repo = String(env.AE_AUTOMATION_REPOSITORY || env.GITHUB_REPOSITORY || '').trim();
  if (!repo) {
    throw new Error('AE_AUTOMATION_REPOSITORY or GITHUB_REPOSITORY is required');
  }

  const sinceDays = toInt(env.AE_AUTOMATION_OBSERVABILITY_SINCE_DAYS, 7, 1);
  const maxRunsPerWorkflow = toInt(env.AE_AUTOMATION_OBSERVABILITY_MAX_RUNS_PER_WORKFLOW, 30, 1);
  const topN = toInt(env.AE_AUTOMATION_OBSERVABILITY_TOP_N, 5, 1);
  const sloTargetPercent = Math.min(100, Math.max(0, toInt(
    env.AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT,
    DEFAULT_SLO_TARGET_PERCENT,
    0,
  )));
  const mttrTargetMinutes = toInt(
    env.AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES,
    DEFAULT_MTTR_TARGET_MINUTES,
    1,
  );
  const outputPath = String(env.AE_AUTOMATION_OBSERVABILITY_OUTPUT || 'artifacts/automation/weekly-failure-summary.json').trim();

  const workflows = parseCsv(env.AE_AUTOMATION_OBSERVABILITY_WORKFLOWS);
  const targetWorkflows = workflows.length > 0 ? workflows : DEFAULT_WORKFLOWS;
  const sinceIso = toIsoCutoff(sinceDays);

  const { reports, warnings, runStats } = collectReportsFromRuns(
    repo,
    targetWorkflows,
    sinceIso,
    maxRunsPerWorkflow,
  );

  const summary = summarizeAutomationReports(reports, {
    topN,
    failureStatuses: DEFAULT_FAILURE_STATUSES,
    sloTargetPercent,
    mttrTargetMinutes,
  });

  const payload = {
    generatedAt: new Date().toISOString(),
    repository: repo,
    config: {
      sinceDays,
      sinceIso,
      maxRunsPerWorkflow,
      topN,
      sloTargetPercent,
      mttrTargetMinutes,
      workflows: targetWorkflows,
      failureStatuses: DEFAULT_FAILURE_STATUSES,
    },
    runStats,
    summary,
    warnings,
  };

  const resolvedOutputPath = writeJsonFile(outputPath, payload);
  const summaryLines = buildSummaryMarkdown({
    repo,
    sinceIso,
    workflows: targetWorkflows,
    runStats,
    summary,
    outputPath: resolvedOutputPath,
  });
  appendStepSummary(summaryLines, env);

  console.log(`[automation-observability-weekly] wrote ${resolvedOutputPath}`);
  console.log(`[automation-observability-weekly] reports=${summary.totalReports} failures=${summary.totalFailures}`);
  if (warnings.length > 0) {
    console.warn(`[automation-observability-weekly] warnings=${warnings.length}`);
  }

  return payload;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}

export {
  DEFAULT_FAILURE_STATUSES,
  DEFAULT_WORKFLOWS,
  REPORT_PREFIX,
  REPORT_SCHEMA,
  buildSummaryMarkdown,
  extractAutomationReportsFromLog,
  formatTopReasonTable,
  joinCountMap,
  summarizeAutomationReports,
  parseEventTimestamp,
  classifyIncidentType,
  buildSloStats,
  buildMttrStats,
  parseCsv,
  toInt,
  toIsoCutoff,
  main,
};
