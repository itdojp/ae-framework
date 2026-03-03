import { execSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';

const VALID_STATUSES = new Set(['success', 'failed', 'skipped']);
const COMMENT_ID_RE = /^[1-9][0-9]*$/;

function normalizeCommentId(value) {
  const raw = String(value || '').trim();
  if (!COMMENT_ID_RE.test(raw)) return null;
  const parsed = Number.parseInt(raw, 10);
  return Number.isFinite(parsed) && parsed > 0 ? parsed : null;
}

function normalizeExecutionStatus(value) {
  const raw = String(value || '').trim().toLowerCase();
  if (raw === 'success' || raw === 'ok' || raw === 'succeeded') return 'success';
  if (raw === 'failed' || raw === 'failure' || raw === 'error') return 'failed';
  if (raw === 'skipped' || raw === 'skip') return 'skipped';
  return null;
}

function normalizeExecutionResults(rawResults, tasks) {
  const byComment = new Map();
  for (const item of Array.isArray(rawResults) ? rawResults : []) {
    const commentId = normalizeCommentId(item?.commentId);
    if (!commentId) continue;
    const status = normalizeExecutionStatus(item?.status);
    if (!status || !VALID_STATUSES.has(status)) continue;
    byComment.set(commentId, {
      commentId,
      status,
      reason: String(item?.reason || '').trim(),
    });
  }

  const normalized = [];
  for (const task of tasks) {
    const commentId = normalizeCommentId(task?.commentId);
    if (!commentId) continue;
    const mapped = byComment.get(commentId);
    if (mapped) {
      normalized.push(mapped);
      continue;
    }
    normalized.push({
      commentId,
      status: 'failed',
      reason: 'missing execution result for actionable task',
    });
  }
  return normalized;
}

function summarizeResults(results) {
  const summary = {
    attempted: 0,
    succeeded: 0,
    failed: 0,
    skipped: 0,
    status: 'skipped',
    results,
  };
  for (const item of results) {
    if (!item) continue;
    summary.attempted += 1;
    if (item.status === 'success') summary.succeeded += 1;
    if (item.status === 'failed') summary.failed += 1;
    if (item.status === 'skipped') summary.skipped += 1;
  }
  if (summary.failed > 0) {
    summary.status = 'failed';
  } else if (summary.succeeded > 0 && summary.failed === 0) {
    summary.status = 'success';
  } else {
    summary.status = 'skipped';
  }
  return summary;
}

function summarizeWithSingleReason(tasks, status, reason) {
  const results = [];
  for (const task of Array.isArray(tasks) ? tasks : []) {
    const commentId = normalizeCommentId(task?.commentId);
    if (!commentId) continue;
    results.push({
      commentId,
      status,
      reason,
    });
  }
  return summarizeResults(results);
}

function parseExecutionPayload(stdout) {
  const raw = String(stdout || '').trim();
  if (!raw) return {};
  try {
    return JSON.parse(raw);
  } catch {
    const lines = raw
      .split('\n')
      .map((line) => line.trim())
      .filter(Boolean);
    if (lines.length === 0) return {};
    try {
      return JSON.parse(lines[lines.length - 1]);
    } catch {
      throw new Error('actionable executor output is not valid JSON');
    }
  }
}

function toExecutorFailureReason(error) {
  const status = Number.isInteger(error?.status) ? `exit=${error.status}` : null;
  const signal = String(error?.signal || '').trim();
  const signalPart = signal ? `signal=${signal}` : null;
  const code = String(error?.code || '').trim();
  const codePart = code && !status ? `code=${code}` : null;
  const details = [status, signalPart, codePart].filter(Boolean).join(', ');
  return details
    ? `actionable executor command failed (${details})`
    : 'actionable executor command failed';
}

function executeActionableTasks(tasks, options = {}) {
  const list = Array.isArray(tasks) ? tasks.filter(Boolean) : [];
  if (list.length === 0) {
    return summarizeResults([]);
  }

  if (options.dryRun) {
    return summarizeWithSingleReason(list, 'skipped', 'dry-run: actionable executor is not executed');
  }

  const command = String(options.command || '').trim();
  if (!command) {
    return summarizeWithSingleReason(
      list,
      'failed',
      'AE_AUTOPILOT_ACTIONABLE_COMMAND is not configured',
    );
  }

  let tempRoot = '';
  let tasksPath = '';
  try {
    tempRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'ae-actionable-executor-'));
    tasksPath = path.join(tempRoot, 'tasks.json');
    fs.writeFileSync(tasksPath, `${JSON.stringify({
      prNumber: options.prNumber || null,
      round: options.round || null,
      tasks: list,
    }, null, 2)}\n`);

    const stdout = execSync(command, {
      env: {
        ...process.env,
        ...(options.env || {}),
        AE_ACTIONABLE_TASKS_JSON: tasksPath,
        AE_ACTIONABLE_PR_NUMBER: String(options.prNumber || ''),
        AE_ACTIONABLE_ROUND: String(options.round || ''),
      },
      shell: true,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    const parsed = parseExecutionPayload(stdout);
    const normalized = normalizeExecutionResults(parsed?.results, list);
    return summarizeResults(normalized);
  } catch (error) {
    return summarizeWithSingleReason(
      list,
      'failed',
      toExecutorFailureReason(error),
    );
  } finally {
    if (tempRoot) {
      fs.rmSync(tempRoot, { recursive: true, force: true });
    }
  }
}

export {
  executeActionableTasks,
  normalizeExecutionResults,
  summarizeResults,
};
