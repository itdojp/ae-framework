#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';

const SCHEMA_VERSION = 'ae-automation-report/v1';

function toInt(raw) {
  const parsed = Number.parseInt(String(raw || '').trim(), 10);
  return Number.isFinite(parsed) ? parsed : null;
}

function buildRunUrl(env = process.env) {
  const serverUrl = String(env.GITHUB_SERVER_URL || '').trim();
  const repository = String(env.GITHUB_REPOSITORY || '').trim();
  const runId = String(env.GITHUB_RUN_ID || '').trim();
  if (!serverUrl || !repository || !runId) {
    return '';
  }
  return `${serverUrl}/${repository}/actions/runs/${runId}`;
}

function buildRunContext(env = process.env) {
  return {
    workflow: String(env.GITHUB_WORKFLOW || '').trim(),
    event: String(env.GITHUB_EVENT_NAME || '').trim(),
    runId: toInt(env.GITHUB_RUN_ID),
    attempt: toInt(env.GITHUB_RUN_ATTEMPT),
    url: buildRunUrl(env),
    repository: String(env.GITHUB_REPOSITORY || '').trim(),
    ref: String(env.GITHUB_REF || '').trim(),
    sha: String(env.GITHUB_SHA || '').trim(),
  };
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

function appendSummary(title, lines, env = process.env) {
  const target = String(env.GITHUB_STEP_SUMMARY || '').trim();
  if (!target) {
    return;
  }
  const dir = path.dirname(target);
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
  const content = [`## ${title}`, ...lines].join('\n') + '\n';
  fs.appendFileSync(target, content, 'utf8');
}

function summarizeReport(report) {
  const lines = [
    `- workflow: ${report.tool}`,
    `- status: ${report.status || 'unknown'}`,
  ];
  if (report.reason) {
    lines.push(`- reason: ${report.reason}`);
  }
  if (report.prNumber) {
    lines.push(`- pr: #${report.prNumber}`);
  }
  if (report.mode) {
    lines.push(`- mode: ${report.mode}`);
  }
  if (report.run?.url) {
    lines.push(`- run: ${report.run.url}`);
  }
  if (report.metrics && typeof report.metrics === 'object') {
    for (const [key, value] of Object.entries(report.metrics)) {
      lines.push(`- ${key}: ${value}`);
    }
  }
  return lines;
}

function emitAutomationReport(input, env = process.env) {
  const report = {
    schemaVersion: SCHEMA_VERSION,
    generatedAt: new Date().toISOString(),
    ...input,
    run: {
      ...buildRunContext(env),
      ...(input && typeof input.run === 'object' ? input.run : {}),
    },
  };

  const jsonLine = JSON.stringify(report);
  console.log(`[ae-automation-report] ${jsonLine}`);

  const configuredPath = String(env.AE_AUTOMATION_REPORT_FILE || '').trim();
  if (configuredPath) {
    const resolvedPath = writeJsonFile(configuredPath, report);
    console.log(`[ae-automation-report] wrote ${resolvedPath}`);
  }

  appendSummary('Automation Report', summarizeReport(report), env);
  return report;
}

export {
  SCHEMA_VERSION,
  buildRunContext,
  buildRunUrl,
  emitAutomationReport,
};
