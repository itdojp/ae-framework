#!/usr/bin/env node

import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { execGh, execGhJson } from './lib/gh-exec.mjs';
import { emitAutomationReport } from './lib/automation-report.mjs';
import { sleep } from './lib/timing.mjs';
import {
  hasLabel as hasOptInLabel,
  isActorAllowed,
  normalizeLabelNames,
  parseActorCsv,
  toActorSet,
} from './lib/automation-guards.mjs';

const marker = '<!-- AE-CODEX-AUTOPILOT v1 -->';
const repo = String(process.env.GITHUB_REPOSITORY || '').trim();
const prNumber = toPositiveInt(process.env.PR_NUMBER || '');
const maxRounds = readIntEnv('AE_AUTOPILOT_MAX_ROUNDS', 3, 1);
const roundWaitSeconds = readIntEnv('AE_AUTOPILOT_ROUND_WAIT_SECONDS', 8, 0);
const dryRun = toBool(process.env.AE_AUTOPILOT_DRY_RUN) || toBool(process.env.DRY_RUN);
const globalDisabled = toBool(process.env.AE_AUTOMATION_GLOBAL_DISABLE);
const copilotActors = parseActorCsv(
  process.env.COPILOT_ACTORS,
  'copilot-pull-request-reviewer,github-copilot,github-copilot[bot],copilot,copilot[bot],Copilot',
);
const copilotActorSet = toActorSet(copilotActors);

function readIntEnv(name, fallback, min) {
  const parsed = Number.parseInt(String(process.env[name] || '').trim(), 10);
  if (!Number.isFinite(parsed) || parsed < min) return fallback;
  return parsed;
}

function toBool(value) {
  const normalized = String(value || '').trim().toLowerCase();
  return normalized === '1' || normalized === 'true' || normalized === 'yes' || normalized === 'on';
}

function toPositiveInt(value) {
  const parsed = Number.parseInt(String(value || '').trim(), 10);
  if (!Number.isFinite(parsed) || parsed <= 0) return null;
  return parsed;
}

function execJson(args, input) {
  return execGhJson(args, { input });
}

function execText(args, input, stdio = ['pipe', 'pipe', 'pipe']) {
  return execGh(args, { input, stdio });
}

function listComments(number) {
  const comments = [];
  let page = 1;
  while (true) {
    const chunk = execJson(['api', `repos/${repo}/issues/${number}/comments?per_page=100&page=${page}`]);
    if (!Array.isArray(chunk) || chunk.length === 0) break;
    comments.push(...chunk);
    if (chunk.length < 100) break;
    page += 1;
  }
  return comments;
}

function upsertComment(number, body) {
  const comments = listComments(number);
  const existing = comments.find((comment) => typeof comment.body === 'string' && comment.body.startsWith(marker));
  const payload = JSON.stringify({ body });
  if (existing) {
    execText(['api', '--method', 'PATCH', `repos/${repo}/issues/comments/${existing.id}`, '--input', '-'], payload);
    return;
  }
  execText(['api', `repos/${repo}/issues/${number}/comments`, '--input', '-'], payload);
}

function setBlocked(number) {
  execText(['issue', 'edit', String(number), '--repo', repo, '--add-label', 'status:blocked', '--add-label', 'ci-stability']);
}

function clearBlocked(number) {
  try {
    execText(['issue', 'edit', String(number), '--repo', repo, '--remove-label', 'status:blocked']);
  } catch {
    // Ignore when label is absent.
  }
}

function hasLabel(pr, labelName) {
  return hasOptInLabel(normalizeLabelNames(pr && pr.labels), labelName);
}

function parseGateStatus(statusCheckRollup) {
  const gateChecks = (statusCheckRollup || []).filter((item) =>
    item.__typename === 'CheckRun'
    && item.name === 'gate'
    && item.workflowName === 'Copilot Review Gate'
  );
  if (gateChecks.length === 0) return 'missing';

  const allHaveCompletedAt = gateChecks.every(
    (item) => item && typeof item.completedAt === 'string' && item.completedAt,
  );
  if (allHaveCompletedAt) {
    const sorted = [...gateChecks].sort(
      (a, b) => new Date(a.completedAt) - new Date(b.completedAt),
    );
    const latest = sorted[sorted.length - 1];
    if (latest.status !== 'COMPLETED') return 'pending';
    return latest.conclusion === 'SUCCESS' ? 'success' : 'failure';
  }

  if (gateChecks.some((item) => item.status !== 'COMPLETED')) return 'pending';
  const conclusions = new Set(
    gateChecks
      .map((item) => item && item.conclusion)
      .filter(Boolean),
  );
  if (conclusions.size === 1) {
    const [only] = conclusions;
    return only === 'SUCCESS' ? 'success' : 'failure';
  }
  return 'failure';
}

function fetchPrView(number) {
  return execJson([
    'pr',
    'view',
    String(number),
    '--repo',
    repo,
    '--json',
    'number,title,url,state,isDraft,mergeable,mergeStateStatus,headRefName,headRefOid,autoMergeRequest,labels,statusCheckRollup',
  ]);
}

function fetchCopilotThreadState(number) {
  const query = `query($owner:String!, $repo:String!, $number:Int!) {\n  repository(owner:$owner, name:$repo) {\n    pullRequest(number:$number) {\n      reviewThreads(first:100) {\n        nodes {\n          isResolved\n          comments(first:100) { nodes { author { login } } }\n        }\n      }\n    }\n  }\n}`;
  const [owner, repoName] = repo.split('/');
  const data = execJson([
    'api',
    'graphql',
    '-f',
    `query=${query}`,
    '-f',
    `owner=${owner}`,
    '-f',
    `repo=${repoName}`,
    '-F',
    `number=${number}`,
  ]);
  const threads = data?.data?.repository?.pullRequest?.reviewThreads?.nodes || [];
  const unresolved = threads.filter((thread) =>
    thread
    && !thread.isResolved
    && Array.isArray(thread.comments?.nodes)
    && thread.comments.nodes.some((comment) =>
      isActorAllowed(comment?.author?.login, copilotActorSet))
  );
  return {
    total: threads.length,
    unresolvedCopilot: unresolved.length,
  };
}

function runAutoFix(pr) {
  const tempRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'ae-codex-autopilot-'));
  const worktreeDir = path.join(tempRoot, 'worktree');
  const runnerDir = path.join(tempRoot, 'runner');
  const ciDir = path.dirname(fileURLToPath(import.meta.url));
  const trustedAutoFixPath = path.join(ciDir, 'copilot-auto-fix.mjs');
  const trustedGhExecPath = path.join(ciDir, 'lib', 'gh-exec.mjs');
  const trustedAutomationReportPath = path.join(ciDir, 'lib', 'automation-report.mjs');
  const trustedGuardsPath = path.join(ciDir, 'lib', 'automation-guards.mjs');
  const runnerAutoFixPath = path.join(runnerDir, 'copilot-auto-fix.mjs');
  const runnerLibDir = path.join(runnerDir, 'lib');

  fs.mkdirSync(runnerLibDir, { recursive: true });
  fs.copyFileSync(trustedAutoFixPath, runnerAutoFixPath);
  fs.copyFileSync(trustedGhExecPath, path.join(runnerLibDir, 'gh-exec.mjs'));
  fs.copyFileSync(trustedAutomationReportPath, path.join(runnerLibDir, 'automation-report.mjs'));
  fs.copyFileSync(trustedGuardsPath, path.join(runnerLibDir, 'automation-guards.mjs'));

  const env = {
    ...process.env,
    PR_NUMBER: String(pr.number),
    PR_HEAD_REF: pr.headRefName,
    PR_HEAD_SHA: pr.headRefOid,
    AE_COPILOT_AUTO_FIX_FORCE: '1',
    AE_COPILOT_AUTO_FIX: '1',
  };
  try {
    execFileSync('git', ['fetch', 'origin', pr.headRefName], { stdio: 'inherit' });
    execFileSync('git', ['worktree', 'add', '--detach', worktreeDir, pr.headRefOid], { stdio: 'inherit' });
    execFileSync('node', [runnerAutoFixPath], { stdio: 'inherit', env, cwd: worktreeDir });
  } finally {
    try {
      execFileSync('git', ['worktree', 'remove', '--force', worktreeDir], { stdio: 'ignore' });
    } catch {
      // Ignore cleanup failure.
    }
    fs.rmSync(tempRoot, { recursive: true, force: true });
  }
}

function dispatchGate(pr) {
  execText([
    'workflow',
    'run',
    'copilot-review-gate.yml',
    '--repo',
    repo,
    '--ref',
    pr.headRefName,
    '-f',
    `pr_number=${pr.number}`,
  ]);
}

function dispatchUpdateBranch(pr) {
  execText([
    'workflow',
    'run',
    'PR Maintenance',
    '--repo',
    repo,
    '-f',
    'mode=update-branch',
    '-f',
    `pr_number=${pr.number}`,
  ]);
}

function enableAutoMerge(pr) {
  const env = {
    ...process.env,
    PR_NUMBER: String(pr.number),
  };
  execFileSync('node', ['scripts/ci/auto-merge-enabler.mjs'], { stdio: 'inherit', env });
}

function renderBody(result) {
  const lines = [
    marker,
    `## Codex Autopilot Lane (${new Date().toISOString()})`,
    `- PR: #${result.number} ${result.title}`.trimEnd(),
    `- status: ${result.status}`,
    `- rounds: ${result.rounds}`,
    `- dry-run: ${dryRun ? 'true' : 'false'}`,
    `- gate: ${result.gateStatus}`,
    `- unresolved copilot threads: ${result.unresolvedCopilot}`,
    `- mergeable: ${result.mergeable || 'UNKNOWN'}`,
    `- merge state: ${result.mergeState || 'UNKNOWN'}`,
  ];
  if (result.reason) lines.push(`- reason: ${result.reason}`);
  if (result.actions.length > 0) {
    lines.push('- actions:');
    for (const action of result.actions) {
      lines.push(`  - ${action}`);
    }
  }
  return `${lines.join('\n')}\n`;
}

async function processPr(number) {
  const actions = [];
  let finalReason = '';
  let finalState = null;
  let done = false;
  let roundsExecuted = 0;

  for (let round = 1; round <= maxRounds; round += 1) {
    roundsExecuted = round;
    const pr = fetchPrView(number);
    finalState = pr;

    if (pr.state === 'MERGED') {
      finalReason = 'already merged';
      done = true;
      break;
    }
    if (pr.isDraft) {
      finalReason = 'draft PR';
      break;
    }
    if (!hasLabel(pr, 'autopilot:on')) {
      finalReason = 'missing label autopilot:on';
      break;
    }
    if (pr.mergeable === 'CONFLICTING' || pr.mergeStateStatus === 'DIRTY') {
      finalReason = 'merge conflict';
      break;
    }

    const threadState = fetchCopilotThreadState(number);
    const gateStatus = parseGateStatus(pr.statusCheckRollup || []);

    if (pr.mergeStateStatus === 'BEHIND') {
      actions.push(`round${round}: dispatch update-branch`);
      if (!dryRun) {
        dispatchUpdateBranch(pr);
      }
    }

    if (threadState.unresolvedCopilot > 0 || gateStatus === 'failure' || gateStatus === 'missing') {
      actions.push(`round${round}: apply copilot auto-fix (force mode)`);
      if (!dryRun) {
        runAutoFix(pr);
      }
      actions.push(`round${round}: dispatch copilot review gate`);
      if (!dryRun) {
        dispatchGate(pr);
      }
    }

    actions.push(`round${round}: evaluate auto-merge eligibility`);
    if (!dryRun) {
      enableAutoMerge(pr);
    }

    const refreshed = fetchPrView(number);
    finalState = refreshed;
    const refreshedThreads = fetchCopilotThreadState(number);
    const refreshedGate = parseGateStatus(refreshed.statusCheckRollup || []);
    if (refreshed.autoMergeRequest) {
      finalReason = 'auto-merge enabled';
      done = true;
      break;
    }
    if (refreshedGate === 'success' && refreshedThreads.unresolvedCopilot === 0 && refreshed.mergeStateStatus !== 'BEHIND') {
      finalReason = 'checks healthy, waiting for required checks/merge queue';
      done = true;
      break;
    }

    if (round < maxRounds && roundWaitSeconds > 0) {
      await sleep(roundWaitSeconds * 1000);
    }
  }

  const finalThreads = finalState ? fetchCopilotThreadState(number) : { unresolvedCopilot: 0 };
  const finalGate = finalState ? parseGateStatus(finalState.statusCheckRollup || []) : 'missing';
  let status = done ? 'done' : 'blocked';
  if (!done && finalReason.startsWith('missing label')) {
    status = 'skip';
  }
  if (!done && finalReason === 'draft PR') {
    status = 'skip';
  }

  const result = {
    number,
    title: finalState?.title || '',
    status,
    reason: finalReason,
    rounds: roundsExecuted,
    actions,
    unresolvedCopilot: finalThreads.unresolvedCopilot,
    gateStatus: finalGate,
    mergeable: finalState?.mergeable || '',
    mergeState: finalState?.mergeStateStatus || '',
  };

  if (status === 'skip') {
    return result;
  }

  if (!dryRun) {
    if (status === 'blocked') {
      setBlocked(number);
    } else {
      clearBlocked(number);
    }
    upsertComment(number, renderBody(result));
  }

  return result;
}

async function main() {
  if (!repo) {
    console.error('[codex-autopilot] GITHUB_REPOSITORY is required.');
    emitAutomationReport({
      tool: 'codex-autopilot-lane',
      mode: dryRun ? 'dry-run' : 'active',
      status: 'error',
      reason: 'GITHUB_REPOSITORY is required',
    });
    process.exit(1);
  }
  if (!prNumber) {
    console.error('[codex-autopilot] PR_NUMBER is required.');
    emitAutomationReport({
      tool: 'codex-autopilot-lane',
      mode: dryRun ? 'dry-run' : 'active',
      status: 'error',
      reason: 'PR_NUMBER is required',
    });
    process.exit(1);
  }
  if (globalDisabled) {
    console.log('[codex-autopilot] Skip: AE_AUTOMATION_GLOBAL_DISABLE is enabled.');
    emitAutomationReport({
      tool: 'codex-autopilot-lane',
      mode: dryRun ? 'dry-run' : 'active',
      status: 'skip',
      reason: 'AE_AUTOMATION_GLOBAL_DISABLE is enabled',
      prNumber,
    });
    return;
  }

  try {
    const result = await processPr(prNumber);
    console.log(`[codex-autopilot] #${result.number}: ${result.status} (${result.reason || 'n/a'})`);
    const reportStatus = result.status === 'done' ? 'resolved' : result.status;
    emitAutomationReport({
      tool: 'codex-autopilot-lane',
      mode: dryRun ? 'dry-run' : 'active',
      status: reportStatus,
      reason: result.reason || '',
      prNumber: result.number,
      metrics: {
        rounds: result.rounds,
        actions: result.actions.length,
        unresolvedCopilot: result.unresolvedCopilot,
        gateStatus: result.gateStatus,
      },
      data: {
        mergeable: result.mergeable,
        mergeState: result.mergeState,
      },
    });
  } catch (error) {
    const message = error && error.message ? error.message : String(error);
    emitAutomationReport({
      tool: 'codex-autopilot-lane',
      mode: dryRun ? 'dry-run' : 'active',
      status: 'error',
      reason: message,
      prNumber,
    });
    throw error;
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}

export { parseGateStatus, hasLabel };
