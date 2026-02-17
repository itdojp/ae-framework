#!/usr/bin/env node

import { execGh, execGhJson } from './lib/gh-exec.mjs';
import { emitAutomationReport } from './lib/automation-report.mjs';
import { readIntEnv, waitForNextRound } from './lib/round-control.mjs';
import { sleep } from './lib/timing.mjs';

const marker = '<!-- AE-SELF-HEAL v1 -->';
const FAILURE_CONCLUSIONS = new Set(['FAILURE', 'CANCELLED', 'TIMED_OUT', 'ACTION_REQUIRED', 'STALE']);

const repo = String(process.env.GITHUB_REPOSITORY || '').trim();
const eventName = String(process.env.GITHUB_EVENT_NAME || '').trim();

const maxRounds = readIntEnv('AE_SELF_HEAL_MAX_ROUNDS', 3, 1);
const maxAgeMinutes = readIntEnv('AE_SELF_HEAL_MAX_AGE_MINUTES', 180, 1);
const maxPrs = readIntEnv('AE_SELF_HEAL_MAX_PRS', 20, 1);
const roundWaitSeconds = readIntEnv('AE_SELF_HEAL_ROUND_WAIT_SECONDS', 60, 0);
const roundWaitStrategy = String(process.env.AE_SELF_HEAL_WAIT_STRATEGY || 'fixed').trim().toLowerCase();
const roundWaitMaxSeconds = readIntEnv('AE_SELF_HEAL_ROUND_WAIT_MAX_SECONDS', roundWaitSeconds, 0);
const dryRun = toBool(process.env.AE_SELF_HEAL_DRY_RUN) || toBool(process.env.SELF_HEAL_DRY_RUN);
const globalDisabled = toBool(process.env.AE_AUTOMATION_GLOBAL_DISABLE);
const targetPr = toPositiveInt(process.env.PR_NUMBER || '');
const workflowRunPr = parseFirstPositiveInt(process.env.WORKFLOW_RUN_PR_NUMBERS || process.env.WORKFLOW_RUN_PR_NUMBER || '');

function toPositiveInt(raw) {
  const parsed = Number.parseInt(String(raw || '').trim(), 10);
  if (!Number.isFinite(parsed) || parsed <= 0) return null;
  return parsed;
}

function parseFirstPositiveInt(raw) {
  const parts = String(raw || '')
    .split(',')
    .map((part) => toPositiveInt(part))
    .filter(Boolean);
  return parts.length > 0 ? parts[0] : null;
}

function toBool(value) {
  const normalized = String(value || '').trim().toLowerCase();
  return normalized === '1' || normalized === 'true' || normalized === 'yes' || normalized === 'on';
}

function parseRunId(detailsUrl) {
  const match = String(detailsUrl || '').match(/\/actions\/runs\/([0-9]+)/);
  return match ? Number.parseInt(match[1], 10) : null;
}

function summarizeCheckRollup(rollup, { nowMs, maxAgeMs, rerunBlacklist }) {
  const counts = {
    success: 0,
    failure: 0,
    pending: 0,
    skipped: 0,
    neutral: 0,
  };
  const rerunnableRunIds = new Set();
  const staleFailures = [];
  const failureNames = [];
  const keyStates = new Map();

  for (const item of rollup || []) {
    if (item.__typename === 'CheckRun') {
      const key = `${item.workflowName || ''}::${item.name || ''}`;
      const stateSet = keyStates.get(key) || new Set();

      if (item.status !== 'COMPLETED') {
        counts.pending += 1;
        stateSet.add('pending');
        keyStates.set(key, stateSet);
        continue;
      }

      if (item.conclusion === 'SUCCESS') {
        counts.success += 1;
        stateSet.add('success');
        keyStates.set(key, stateSet);
        continue;
      }

      if (FAILURE_CONCLUSIONS.has(item.conclusion || '')) {
        counts.failure += 1;
        stateSet.add('failure');
        keyStates.set(key, stateSet);
        const runId = parseRunId(item.detailsUrl);
        const completedAtMs = Date.parse(item.completedAt || '');
        const ageMs = Number.isFinite(completedAtMs) ? Math.max(0, nowMs - completedAtMs) : 0;
        if (runId && !rerunBlacklist.has(runId) && ageMs <= maxAgeMs) {
          rerunnableRunIds.add(runId);
        } else {
          staleFailures.push({
            workflow: item.workflowName || '',
            name: item.name || '',
            runId,
            ageMs,
          });
        }
        failureNames.push(`${item.workflowName || 'workflow'} / ${item.name || 'check'}`);
        continue;
      }

      if (item.conclusion === 'SKIPPED') {
        counts.skipped += 1;
        stateSet.add('skipped');
      } else {
        counts.neutral += 1;
        stateSet.add('neutral');
      }
      keyStates.set(key, stateSet);
      continue;
    }

    if (item.__typename === 'StatusContext') {
      const key = `status-context::${item.context || ''}`;
      const stateSet = keyStates.get(key) || new Set();

      if (item.state === 'SUCCESS') {
        counts.success += 1;
        stateSet.add('success');
      } else if (item.state === 'PENDING') {
        counts.pending += 1;
        stateSet.add('pending');
      } else if (item.state === 'FAILURE' || item.state === 'ERROR') {
        counts.failure += 1;
        stateSet.add('failure');
        failureNames.push(item.context || 'status-context');
      } else {
        counts.neutral += 1;
        stateSet.add('neutral');
      }
      keyStates.set(key, stateSet);
    }
  }

  const mixedKeys = [];
  for (const [key, states] of keyStates.entries()) {
    if (states.has('success') && states.has('failure')) {
      mixedKeys.push(key);
    }
  }

  return {
    counts,
    rerunnableRunIds: Array.from(rerunnableRunIds),
    staleFailures,
    failureNames: Array.from(new Set(failureNames)),
    mixedKeys,
  };
}

function classifyPr(view, context) {
  const maxAgeMs = context.maxAgeMinutes * 60 * 1000;
  const checkSummary = summarizeCheckRollup(view.statusCheckRollup || [], {
    nowMs: context.nowMs,
    maxAgeMs,
    rerunBlacklist: context.rerunBlacklist || new Set(),
  });

  const mergeState = String(view.mergeStateStatus || '');
  const mergeable = String(view.mergeable || '');
  const isBehind = mergeState === 'BEHIND';
  const hasConflict = mergeable === 'CONFLICTING' || mergeState === 'DIRTY';

  return {
    number: view.number,
    title: view.title || '',
    url: view.url || '',
    isDraft: Boolean(view.isDraft),
    mergeable,
    mergeState,
    isBehind,
    hasConflict,
    checkSummary,
  };
}

function planActions(state) {
  if (state.isDraft) {
    return { status: 'skip', reason: 'draft', actions: [] };
  }
  if (state.hasConflict) {
    return {
      status: 'blocked',
      reason: `conflict (mergeable=${state.mergeable || 'UNKNOWN'}, mergeState=${state.mergeState || 'UNKNOWN'})`,
      actions: [],
    };
  }

  const actions = [];
  if (state.isBehind) {
    actions.push({ type: 'update-branch' });
  }
  if (state.checkSummary.rerunnableRunIds.length > 0) {
    actions.push({ type: 'rerun-failed', runIds: state.checkSummary.rerunnableRunIds });
  }

  if (actions.length > 0) {
    return { status: 'actionable', reason: '', actions };
  }

  if (state.checkSummary.counts.failure > 0) {
    return {
      status: 'blocked',
      reason: 'no rerunnable failed checks remain (stale, missing runId, or already rerun)',
      actions: [],
    };
  }

  return { status: 'healthy', reason: '', actions: [] };
}

function execJson(args, input) {
  return execGhJson(args, { input });
}

function execText(args, input) {
  return execGh(args, { input });
}

function listComments(prNumber) {
  const comments = [];
  let page = 1;
  while (true) {
    const chunk = execJson([
      'api',
      `repos/${repo}/issues/${prNumber}/comments?per_page=100&page=${page}`,
    ]);
    if (!Array.isArray(chunk) || chunk.length === 0) break;
    comments.push(...chunk);
    if (chunk.length < 100) break;
    page += 1;
  }
  return comments;
}

function upsertComment(prNumber, body) {
  const payload = JSON.stringify({ body });
  const comments = listComments(prNumber);
  const existing = comments.find(
    (item) => typeof item.body === 'string' && item.body.startsWith(marker)
  );
  if (existing) {
    execText(['api', '--method', 'PATCH', `repos/${repo}/issues/comments/${existing.id}`, '--input', '-'], payload);
    return;
  }
  execText(['api', `repos/${repo}/issues/${prNumber}/comments`, '--input', '-'], payload);
}

function setBlockedLabels(prNumber) {
  execText(['issue', 'edit', String(prNumber), '--repo', repo, '--add-label', 'status:blocked', '--add-label', 'ci-stability']);
}

function clearBlockedLabel(prNumber) {
  try {
    execText(['issue', 'edit', String(prNumber), '--repo', repo, '--remove-label', 'status:blocked']);
  } catch {
    // Ignore: label may not exist.
  }
}

function fetchPrView(prNumber) {
  return execJson([
    'pr',
    'view',
    String(prNumber),
    '--repo',
    repo,
    '--json',
    'number,title,url,isDraft,mergeable,mergeStateStatus,statusCheckRollup',
  ]);
}

function dispatchUpdateBranch(prNumber) {
  execText([
    'workflow',
    'run',
    'PR Maintenance',
    '--repo',
    repo,
    '-f',
    'mode=update-branch',
    '-f',
    `pr_number=${prNumber}`,
  ]);
}

function rerunFailed(runId) {
  execText(['run', 'rerun', String(runId), '--repo', repo, '--failed']);
}

function renderBody(result) {
  const lines = [
    marker,
    `## PR Self-Heal (${new Date().toISOString()})`,
    `- PR: #${result.number} ${result.title}`.trimEnd(),
    `- status: ${result.status}`,
    `- rounds: ${result.rounds}`,
    `- dry-run: ${dryRun ? 'true' : 'false'}`,
    `- mergeable: ${result.mergeable || 'UNKNOWN'}`,
    `- merge state: ${result.mergeState || 'UNKNOWN'}`,
    `- checks: success=${result.checks.success}, failure=${result.checks.failure}, pending=${result.checks.pending}`,
  ];
  if (result.reason) {
    lines.push(`- reason: ${result.reason}`);
  }
  if (result.actions.length > 0) {
    lines.push('- actions:');
    for (const action of result.actions) {
      lines.push(`  - ${action}`);
    }
  }
  if (result.failures.length > 0) {
    lines.push('- failed checks (sample):');
    for (const failure of result.failures.slice(0, 6)) {
      lines.push(`  - ${failure}`);
    }
  }
  return `${lines.join('\n')}\n`;
}

async function processPr(prNumber) {
  const rerunBlacklist = new Set();
  const actionsTaken = [];
  let finalState = null;
  let finalReason = '';
  let roundsExecuted = 0;
  let lastRoundExecutedActions = false;

  for (let round = 1; round <= maxRounds; round += 1) {
    roundsExecuted = round;
    const view = fetchPrView(prNumber);
    const state = classifyPr(view, {
      nowMs: Date.now(),
      maxAgeMinutes,
      rerunBlacklist,
    });
    finalState = state;
    const plan = planActions(state);

    if (plan.status === 'healthy' || plan.status === 'skip') {
      finalReason = plan.reason;
      break;
    }

    if (plan.actions.length === 0) {
      finalReason = plan.reason;
      break;
    }

    lastRoundExecutedActions = true;
    for (const action of plan.actions) {
      if (action.type === 'update-branch') {
        actionsTaken.push(`round${round}: update-branch dispatch`);
        if (!dryRun) {
          dispatchUpdateBranch(prNumber);
        }
      }
      if (action.type === 'rerun-failed') {
        for (const runId of action.runIds) {
          rerunBlacklist.add(runId);
          actionsTaken.push(`round${round}: rerun failed run ${runId}`);
          if (!dryRun) {
            rerunFailed(runId);
          }
        }
      }
    }

    await waitForNextRound({
      round,
      maxRounds,
      baseSeconds: roundWaitSeconds,
      strategy: roundWaitStrategy,
      maxSeconds: roundWaitMaxSeconds,
    });
  }

  if (!finalState) {
    return null;
  }

  const finalPlan = planActions(finalState);
  let finalStatus = finalPlan.status === 'healthy' ? 'resolved' : finalPlan.status;
  let reason = finalReason || finalPlan.reason;
  if (finalStatus === 'actionable') {
    finalStatus = 'blocked';
    if (!reason) {
      reason = lastRoundExecutedActions
        ? 'max rounds reached with pending actions; follow-up run required'
        : 'actionable state remained after max rounds';
    }
  }

  if (!dryRun) {
    if (finalStatus === 'resolved' || finalStatus === 'skip') {
      clearBlockedLabel(prNumber);
    } else if (finalStatus === 'blocked') {
      setBlockedLabels(prNumber);
    }
  }

  const result = {
    number: finalState.number,
    title: finalState.title,
    status: finalStatus,
    reason,
    rounds: roundsExecuted,
    mergeable: finalState.mergeable,
    mergeState: finalState.mergeState,
    checks: finalState.checkSummary.counts,
    failures: finalState.checkSummary.failureNames,
    actions: actionsTaken,
  };

  if (!dryRun) {
    upsertComment(prNumber, renderBody(result));
  }

  return result;
}

function listOpenPrNumbers(limit) {
  const rows = execJson([
    'pr',
    'list',
    '--repo',
    repo,
    '--state',
    'open',
    '--limit',
    String(limit),
    '--json',
    'number',
  ]);
  return Array.isArray(rows) ? rows.map((row) => row.number).filter((n) => Number.isFinite(n)) : [];
}

async function main() {
  if (!repo) {
    console.error('[pr-self-heal] GITHUB_REPOSITORY is required.');
    process.exit(1);
  }
  if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repo)) {
    console.error('[pr-self-heal] GITHUB_REPOSITORY format is invalid.');
    process.exit(1);
  }
  if (globalDisabled) {
    console.log('[pr-self-heal] Skip: AE_AUTOMATION_GLOBAL_DISABLE is enabled.');
    emitAutomationReport({
      tool: 'pr-self-heal',
      mode: dryRun ? 'dry-run' : 'active',
      status: 'skip',
      reason: 'AE_AUTOMATION_GLOBAL_DISABLE is enabled',
      metrics: {
        targets: 0,
        processed: 0,
      },
    });
    return;
  }

  const targets = [];
  let targetSource = 'scan';
  if (targetPr) {
    targets.push(targetPr);
    targetSource = 'pr_number';
  } else if (workflowRunPr) {
    targets.push(workflowRunPr);
    targetSource = 'workflow_run';
  } else if (eventName === 'workflow_run') {
    console.log('[pr-self-heal] workflow_run has no associated pull request; skipping global scan.');
    emitAutomationReport({
      tool: 'pr-self-heal',
      mode: dryRun ? 'dry-run' : 'active',
      status: 'skip',
      reason: 'workflow_run has no associated pull request',
      metrics: {
        targets: 0,
        processed: 0,
      },
    });
    return;
  } else {
    targets.push(...listOpenPrNumbers(maxPrs));
  }

  if (targets.length === 0) {
    console.log('[pr-self-heal] No PR targets found.');
    emitAutomationReport({
      tool: 'pr-self-heal',
      mode: dryRun ? 'dry-run' : 'active',
      status: 'skip',
      reason: 'no PR targets found',
      metrics: {
        targets: 0,
        processed: 0,
      },
    });
    return;
  }

  const results = [];
  const failures = [];
  for (const number of targets) {
    try {
      const result = await processPr(number);
      if (!result) {
        console.log(`[pr-self-heal] #${number}: skipped (no state).`);
        results.push({
          number,
          status: 'skip',
          reason: 'no state',
        });
        continue;
      }
      console.log(`[pr-self-heal] #${number}: ${result.status} (${result.reason || 'n/a'})`);
      results.push({
        number,
        status: result.status,
        reason: result.reason || '',
        rounds: result.rounds,
      });
    } catch (error) {
      const message = error && error.message ? error.message : String(error);
      console.error(`[pr-self-heal] #${number}: failed - ${message}`);
      failures.push({ number, message });
    }
    await sleep(300);
  }

  const blocked = results.filter((item) => item.status === 'blocked').length;
  const resolved = results.filter((item) => item.status === 'resolved').length;
  const skipped = results.filter((item) => item.status === 'skip').length;
  let status = 'resolved';
  let reason = 'completed';
  if (failures.length > 0) {
    status = 'error';
    reason = `${failures.length} target(s) failed`;
  } else if (blocked > 0) {
    status = 'blocked';
    reason = `${blocked} target(s) blocked`;
  } else if (resolved === 0 && skipped > 0) {
    status = 'skip';
    reason = 'all targets skipped';
  }

  emitAutomationReport({
    tool: 'pr-self-heal',
    mode: dryRun ? 'dry-run' : 'active',
    status,
    reason,
    metrics: {
      targets: targets.length,
      processed: results.length,
      resolved,
      blocked,
      skipped,
      errors: failures.length,
    },
    data: {
      targetSource,
      results,
      failures,
    },
  });
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}

export { parseRunId, summarizeCheckRollup, classifyPr, planActions };
