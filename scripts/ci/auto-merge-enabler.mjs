#!/usr/bin/env node
import { execFileSync } from 'node:child_process';

const repo = process.env.GITHUB_REPOSITORY;
if (!repo) {
  console.error('[auto-merge-enabler] GITHUB_REPOSITORY is required.');
  process.exit(1);
}
if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repo)) {
  console.error('[auto-merge-enabler] GITHUB_REPOSITORY format is invalid.');
  process.exit(1);
}

const marker = '<!-- AE-AUTO-MERGE-STATUS v1 -->';
const PR_LIMIT = 50;
const PR_SLEEP_MS = 150;
const FAILED_LIST_LIMIT = 5;

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

const execJson = (args, input) => {
  try {
    const output = execFileSync('gh', args, {
      encoding: 'utf8',
      stdio: ['pipe', 'pipe', 'pipe'],
      input,
    });
    return JSON.parse(output);
  } catch (error) {
    console.error(
      '[auto-merge-enabler] gh failed:',
      error && error.message ? error.message : String(error)
    );
    throw error;
  }
};

const fetchRequiredContexts = (repoName, baseRefName) => {
  try {
    const contexts = execJson([
      'api',
      `repos/${repoName}/branches/${baseRefName}/protection/required_status_checks/contexts`,
    ]);
    return Array.isArray(contexts) ? contexts : [];
  } catch (error) {
    const message = error && error.message ? error.message : String(error);
    if (message.includes('Not Found') || message.includes('404')) {
      return [];
    }
    console.error('[auto-merge-enabler] Failed to fetch required status checks:', message);
    return null;
  }
};

const summarizeChecks = (rollup = [], requiredContexts = []) => {
  const counts = { success: 0, failure: 0, pending: 0, skipped: 0, neutral: 0 };
  const failed = [];
  const requiredSet = new Set(requiredContexts);
  for (const item of rollup) {
    if (item.__typename === 'CheckRun') {
      if (requiredSet.size > 0 && !requiredSet.has(item.name)) continue;
      if (item.status !== 'COMPLETED') {
        counts.pending += 1;
        continue;
      }
      switch (item.conclusion) {
        case 'SUCCESS':
          counts.success += 1;
          break;
        case 'FAILURE':
        case 'CANCELLED':
        case 'TIMED_OUT':
        case 'ACTION_REQUIRED':
        case 'STALE':
          counts.failure += 1;
          failed.push(item.name);
          break;
        case 'SKIPPED':
          counts.skipped += 1;
          break;
        default:
          counts.neutral += 1;
          break;
      }
      continue;
    }
    if (item.__typename === 'StatusContext') {
      if (requiredSet.size > 0 && !requiredSet.has(item.context)) continue;
      switch (item.state) {
        case 'SUCCESS':
          counts.success += 1;
          break;
        case 'PENDING':
          counts.pending += 1;
          break;
        case 'FAILURE':
        case 'ERROR':
          counts.failure += 1;
          failed.push(item.context);
          break;
        default:
          counts.neutral += 1;
          break;
      }
    }
  }
  return { counts, failed: failed.slice(0, FAILED_LIST_LIMIT) };
};

const listOpenPrs = () =>
  execJson(['pr', 'list', '--state', 'open', '--limit', String(PR_LIMIT), '--json', 'number,title']);

const buildStatusBody = (pr, view, reasons, summary) => {
  const lines = [
    marker,
    `## Auto-merge Status (${new Date().toISOString()})`,
    `- #${pr.number} ${pr.title}`,
    `- mergeable: ${view.mergeable || 'UNKNOWN'}`,
    `- review: ${view.reviewDecision || 'NONE'}`,
    `- checks: ✅${summary.counts.success} ❌${summary.counts.failure} ⏳${summary.counts.pending}`,
  ];
  if (summary.failed.length > 0) {
    lines.push(`- failed checks: ${summary.failed.join(', ')}`);
  }
  if (reasons.length > 0) {
    lines.push(`- reason: ${reasons.join('; ')}`);
  }
  if (view.autoMergeRequest) {
    lines.push('- auto-merge: already enabled');
  }
  return `${lines.join('\n')}\n`;
};

const upsertComment = (number, body) => {
  const comments = execJson(['api', `repos/${repo}/issues/${number}/comments`]);
  const existing = comments.find((comment) => comment.body && comment.body.startsWith(marker));
  const payload = JSON.stringify({ body });
  if (existing) {
    execFileSync('gh', ['api', '--method', 'PATCH', `repos/${repo}/issues/comments/${existing.id}`, '--input', '-'], {
      stdio: ['pipe', 'inherit', 'inherit'],
      input: payload,
    });
    return;
  }
  execFileSync('gh', ['api', `repos/${repo}/issues/${number}/comments`, '--input', '-'], {
    stdio: ['pipe', 'inherit', 'inherit'],
    input: payload,
  });
};

const enableAutoMerge = (number) => {
  execFileSync('gh', ['pr', 'merge', String(number), '--repo', repo, '--auto', '--squash'], {
    stdio: 'inherit',
  });
};

const main = async () => {
  const prs = listOpenPrs();
  for (const pr of prs) {
    try {
      const view = execJson([
        'pr',
        'view',
        String(pr.number),
        '--repo',
        repo,
        '--json',
        'number,title,mergeable,reviewDecision,statusCheckRollup,baseRefName,isDraft,autoMergeRequest',
      ]);
      const requiredContexts = fetchRequiredContexts(repo, view.baseRefName);
      if (requiredContexts === null) {
        upsertComment(pr.number, buildStatusBody(pr, view, ['required status checks unavailable'], {
          counts: { success: 0, failure: 0, pending: 0 },
          failed: [],
        }));
        await sleep(PR_SLEEP_MS);
        continue;
      }
      const summary = summarizeChecks(view.statusCheckRollup || [], requiredContexts);
      const reasons = [];
      if (view.isDraft) reasons.push('draft');
      if (view.mergeable !== 'MERGEABLE') reasons.push(`mergeable=${view.mergeable || 'UNKNOWN'}`);
      if (view.reviewDecision !== 'APPROVED') reasons.push(`review=${view.reviewDecision || 'NONE'}`);
      if (summary.counts.failure > 0) reasons.push('checks failed');
      if (summary.counts.pending > 0) reasons.push('checks pending');

      if (reasons.length === 0 && !view.autoMergeRequest) {
        try {
          enableAutoMerge(pr.number);
        } catch (error) {
          const message = error && error.message ? error.message : String(error);
          reasons.push(`auto-merge enable failed: ${message}`);
        }
      }
      const body = buildStatusBody(pr, view, reasons, summary);
      upsertComment(pr.number, body);
    } catch (error) {
      console.error(`[auto-merge-enabler] Failed to process PR #${pr.number}:`, error);
    }
    await sleep(PR_SLEEP_MS);
  }
};

await main();
