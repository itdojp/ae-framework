#!/usr/bin/env node

import { execFileSync } from 'node:child_process';
import { execGh, execGhJson } from './lib/gh-exec.mjs';

const marker = '<!-- AE-CODEX-AUTOPILOT v1 -->';
const repo = String(process.env.GITHUB_REPOSITORY || '').trim();
const prNumber = toPositiveInt(process.env.PR_NUMBER || '');
const maxRounds = readIntEnv('AE_AUTOPILOT_MAX_ROUNDS', 3, 1);
const roundWaitSeconds = readIntEnv('AE_AUTOPILOT_ROUND_WAIT_SECONDS', 8, 0);
const dryRun = toBool(process.env.AE_AUTOPILOT_DRY_RUN) || toBool(process.env.DRY_RUN);
const copilotActors = (process.env.COPILOT_ACTORS
  || 'copilot-pull-request-reviewer,github-copilot,github-copilot[bot],copilot,copilot[bot],Copilot')
  .split(',')
  .map((value) => value.trim())
  .filter(Boolean);

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

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
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
  return Array.isArray(pr.labels) && pr.labels.some((label) => label && label.name === labelName);
}

function parseGateStatus(statusCheckRollup) {
  const gateChecks = (statusCheckRollup || []).filter((item) =>
    item.__typename === 'CheckRun'
    && item.name === 'gate'
    && item.workflowName === 'Copilot Review Gate'
  );
  if (gateChecks.length === 0) return 'missing';
  if (gateChecks.some((item) => item.status !== 'COMPLETED')) return 'pending';
  if (gateChecks.some((item) => item.conclusion === 'SUCCESS')) return 'success';
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
  const query = `query($owner:String!, $repo:String!, $number:Int!) {\n  repository(owner:$owner, name:$repo) {\n    pullRequest(number:$number) {\n      reviewThreads(first:100) {\n        nodes {\n          isResolved\n          comments(first:25) { nodes { author { login } } }\n        }\n      }\n    }\n  }\n}`;
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
    && thread.comments.nodes.some((comment) => copilotActors.includes(comment?.author?.login || ''))
  );
  return {
    total: threads.length,
    unresolvedCopilot: unresolved.length,
  };
}

function ensureHeadCheckedOut(pr) {
  const current = execFileSync('git', ['rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
  if (current === pr.headRefOid) return;
  execFileSync('git', ['fetch', 'origin', pr.headRefName], { stdio: 'inherit' });
  execFileSync('git', ['checkout', '--detach', pr.headRefOid], { stdio: 'inherit' });
}

function runAutoFix(pr) {
  ensureHeadCheckedOut(pr);
  const env = {
    ...process.env,
    PR_NUMBER: String(pr.number),
    PR_HEAD_REF: pr.headRefName,
    PR_HEAD_SHA: pr.headRefOid,
    AE_COPILOT_AUTO_FIX_FORCE: '1',
    AE_COPILOT_AUTO_FIX: '1',
  };
  execFileSync('node', ['scripts/ci/copilot-auto-fix.mjs'], { stdio: 'inherit', env });
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

  for (let round = 1; round <= maxRounds; round += 1) {
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
    rounds: maxRounds,
    actions,
    unresolvedCopilot: finalThreads.unresolvedCopilot,
    gateStatus: finalGate,
    mergeable: finalState?.mergeable || '',
    mergeState: finalState?.mergeStateStatus || '',
  };

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
    process.exit(1);
  }
  if (!prNumber) {
    console.error('[codex-autopilot] PR_NUMBER is required.');
    process.exit(1);
  }

  const result = await processPr(prNumber);
  console.log(`[codex-autopilot] #${result.number}: ${result.status} (${result.reason || 'n/a'})`);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}

export { parseGateStatus, hasLabel };
