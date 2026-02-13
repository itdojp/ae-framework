#!/usr/bin/env node
import { execGh, execGhJson } from './lib/gh-exec.mjs';
import { emitAutomationReport } from './lib/automation-report.mjs';

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

const AUTO_MERGE_ENABLED = String(process.env.AE_AUTO_MERGE || '').trim() === '1';
const AUTO_MERGE_MODE = String(process.env.AE_AUTO_MERGE_MODE || 'all').toLowerCase();
const AUTO_MERGE_LABEL = String(process.env.AE_AUTO_MERGE_LABEL || '').trim();
const PR_NUMBER_RAW = process.env.PR_NUMBER !== undefined ? String(process.env.PR_NUMBER).trim() : '';
let PR_NUMBER = null;
if (PR_NUMBER_RAW !== '') {
  if (!/^[1-9][0-9]*$/.test(PR_NUMBER_RAW)) {
    console.error(`[auto-merge-enabler] PR_NUMBER is invalid: ${PR_NUMBER_RAW}`);
    process.exit(1);
  }
  PR_NUMBER = Number(PR_NUMBER_RAW);
}

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

const execJson = (args, input) => {
  try {
    return execGhJson(args, { input });
  } catch (error) {
    console.error(
      '[auto-merge-enabler] gh failed:',
      error && error.message ? error.message : String(error)
    );
    throw error;
  }
};

const encodeRef = (refName) => encodeURIComponent(String(refName || ''));

const fetchBranchMeta = (repoName, baseRefName) => {
  try {
    const encodedRef = encodeRef(baseRefName);
    const branch = execJson(['api', `repos/${repoName}/branches/${encodedRef}`]);
    return { protected: Boolean(branch && branch.protected) };
  } catch (error) {
    const message = error && error.message ? error.message : String(error);
    console.error('[auto-merge-enabler] Failed to fetch branch metadata:', message);
    return null;
  }
};

const fetchProtectionSummary = (repoName, baseRefName, branchMeta) => {
  try {
    if (branchMeta && branchMeta.protected === false) {
      return {
        requiredContexts: [],
        reviewRequirement: { approvalRequired: false, requiredApprovals: 0 },
      };
    }
    const encodedRef = encodeRef(baseRefName);
    const protection = execJson(['api', `repos/${repoName}/branches/${encodedRef}/protection`]);
    const requiredContexts = Array.isArray(protection?.required_status_checks?.contexts)
      ? protection.required_status_checks.contexts
      : [];
    const reviews = protection && protection.required_pull_request_reviews;
    if (!reviews) {
      return {
        requiredContexts,
        reviewRequirement: { approvalRequired: false, requiredApprovals: 0 },
      };
    }
    const requiredApprovals = Number(reviews.required_approving_review_count ?? 0);
    const requireCodeOwnerReviews = Boolean(reviews.require_code_owner_reviews);
    const requireLastPushApproval = Boolean(reviews.require_last_push_approval);
    const approvalRequired =
      (Number.isFinite(requiredApprovals) && requiredApprovals > 0) ||
      requireCodeOwnerReviews ||
      requireLastPushApproval;
    return {
      requiredContexts,
      reviewRequirement: {
        approvalRequired,
        requiredApprovals: Number.isFinite(requiredApprovals) ? requiredApprovals : 0,
      },
    };
  } catch (error) {
    const message = error && error.message ? error.message : String(error);
    if (message.includes('Not Found') || message.includes('404')) {
      // If the branch is protected but protection metadata is not accessible, fail closed.
      if (branchMeta && branchMeta.protected) {
        return null;
      }
      return {
        requiredContexts: [],
        reviewRequirement: { approvalRequired: false, requiredApprovals: 0 },
      };
    }
    console.error('[auto-merge-enabler] Failed to fetch branch protection:', message);
    return null;
  }
};

const summarizeChecks = (rollup = [], requiredContexts) => {
  const counts = { success: 0, failure: 0, pending: 0, skipped: 0, neutral: 0 };
  const failed = [];
  const requiredSet = Array.isArray(requiredContexts) ? new Set(requiredContexts) : null;
  for (const item of rollup) {
    if (item.__typename === 'CheckRun') {
      if (requiredSet && requiredSet.size > 0 && !requiredSet.has(item.name)) continue;
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
      if (requiredSet && requiredSet.size > 0 && !requiredSet.has(item.context)) continue;
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

const listComments = (number) => {
  const comments = [];
  let page = 1;
  while (true) {
    const chunk = execJson([
      'api',
      `repos/${repo}/issues/${number}/comments?per_page=100&page=${page}`,
    ]);
    if (!Array.isArray(chunk) || chunk.length === 0) break;
    comments.push(...chunk);
    if (chunk.length < 100) break;
    page += 1;
  }
  return comments;
};

const listOpenPrs = () =>
  execJson(['pr', 'list', '--state', 'open', '--limit', String(PR_LIMIT), '--json', 'number,title']);

const buildStatusBody = (pr, view, reasons, summary, reviewRequirement) => {
  const reviewRequiredLabel = reviewRequirement
    ? (reviewRequirement.approvalRequired
      ? (reviewRequirement.requiredApprovals > 0 ? `yes/${reviewRequirement.requiredApprovals}` : 'yes')
      : 'no')
    : 'unknown';
  const lines = [
    marker,
    `## Auto-merge Status (${new Date().toISOString()})`,
    `- #${pr.number} ${view.title || pr.title || ''}`.trimEnd(),
    `- mergeable: ${view.mergeable || 'UNKNOWN'}`,
    `- review: ${view.reviewDecision || 'NONE'} (required: ${reviewRequiredLabel})`,
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
  const comments = listComments(number);
  const existing = comments.find(
    (comment) => comment.body && typeof comment.body === 'string' && comment.body.startsWith(marker)
  );
  const payload = JSON.stringify({ body });
  if (existing) {
    execGh(['api', '--method', 'PATCH', `repos/${repo}/issues/comments/${existing.id}`, '--input', '-'], {
      input: payload,
    });
    return;
  }
  execGh(['api', `repos/${repo}/issues/${number}/comments`, '--input', '-'], { input: payload });
};

const enableAutoMerge = (number) => {
  execGh(['pr', 'merge', String(number), '--repo', repo, '--auto', '--squash'], { stdio: 'inherit' });
};

const main = async () => {
  if (!AUTO_MERGE_ENABLED) {
    console.log('[auto-merge-enabler] Skip: AE_AUTO_MERGE is disabled after config resolution.');
    emitAutomationReport({
      tool: 'auto-merge-enabler',
      mode: AUTO_MERGE_MODE || 'all',
      status: 'skip',
      reason: 'AE_AUTO_MERGE is disabled after config resolution',
      metrics: {
        targets: 0,
      },
    });
    return;
  }

  const prs = PR_NUMBER ? [{ number: PR_NUMBER, title: '' }] : listOpenPrs();
  const results = [];
  const failures = [];
  for (const pr of prs) {
    try {
      const view = execJson([
        'pr',
        'view',
        String(pr.number),
        '--repo',
        repo,
        '--json',
        'number,title,mergeable,reviewDecision,statusCheckRollup,baseRefName,isDraft,autoMergeRequest,labels',
      ]);
      const branchMeta = fetchBranchMeta(repo, view.baseRefName);
      if (branchMeta === null) {
        results.push({
          number: pr.number,
          status: 'blocked',
          reason: 'branch metadata unavailable',
        });
        upsertComment(
          pr.number,
          buildStatusBody(pr, view, ['branch metadata unavailable'], {
            counts: { success: 0, failure: 0, pending: 0 },
            failed: [],
          }, null)
        );
        await sleep(PR_SLEEP_MS);
        continue;
      }
      const protectionSummary = fetchProtectionSummary(repo, view.baseRefName, branchMeta);
      if (protectionSummary === null) {
        results.push({
          number: pr.number,
          status: 'blocked',
          reason: 'branch protection unavailable',
        });
        upsertComment(pr.number, buildStatusBody(pr, view, ['branch protection unavailable'], {
          counts: { success: 0, failure: 0, pending: 0 },
          failed: [],
        }, null));
        await sleep(PR_SLEEP_MS);
        continue;
      }
      const { requiredContexts, reviewRequirement } = protectionSummary;
      const summaryAll = summarizeChecks(view.statusCheckRollup || [], null);
      const summaryRequired = requiredContexts.length > 0
        ? summarizeChecks(view.statusCheckRollup || [], requiredContexts)
        : { counts: { success: 0, failure: 0, pending: 0, skipped: 0, neutral: 0 }, failed: [] };
      const reasons = [];
      if (view.isDraft) reasons.push('draft');
      if (view.mergeable !== 'MERGEABLE') reasons.push(`mergeable=${view.mergeable || 'UNKNOWN'}`);
      if (AUTO_MERGE_MODE === 'label') {
        if (!AUTO_MERGE_LABEL) {
          reasons.push('auto-merge label mode but AE_AUTO_MERGE_LABEL is empty');
        } else {
          const labels = Array.isArray(view.labels) ? view.labels.map((l) => l && l.name).filter(Boolean) : [];
          if (!labels.includes(AUTO_MERGE_LABEL)) {
            reasons.push(`missing label=${AUTO_MERGE_LABEL}`);
          }
        }
      } else if (AUTO_MERGE_MODE !== 'all') {
        reasons.push(`unknown AE_AUTO_MERGE_MODE=${AUTO_MERGE_MODE}`);
      }
      if (reviewRequirement.approvalRequired && view.reviewDecision !== 'APPROVED') {
        reasons.push(`review=${view.reviewDecision || 'NONE'}`);
      }
      if (summaryRequired.counts.failure > 0) reasons.push('checks failed');
      if (summaryRequired.counts.pending > 0) reasons.push('checks pending');

      let status = 'blocked';
      let statusReason = reasons.join('; ');
      if (reasons.length === 0 && !view.autoMergeRequest) {
        try {
          enableAutoMerge(pr.number);
          status = 'enabled';
          statusReason = 'auto-merge enabled';
        } catch (error) {
          const message = error && error.message ? error.message : String(error);
          reasons.push(`auto-merge enable failed: ${message}`);
          statusReason = reasons.join('; ');
        }
      } else if (view.autoMergeRequest && reasons.length === 0) {
        status = 'already-enabled';
        statusReason = 'auto-merge already enabled';
      }
      const body = buildStatusBody(pr, view, reasons, summaryAll, reviewRequirement);
      upsertComment(pr.number, body);
      results.push({
        number: pr.number,
        status,
        reason: statusReason,
      });
    } catch (error) {
      console.error(`[auto-merge-enabler] Failed to process PR #${pr.number}:`, error);
      const message = error && error.message ? error.message : String(error);
      failures.push({
        number: pr.number,
        message,
      });
    }
    await sleep(PR_SLEEP_MS);
  }

  const enabled = results.filter((item) => item.status === 'enabled').length;
  const alreadyEnabled = results.filter((item) => item.status === 'already-enabled').length;
  const blocked = results.filter((item) => item.status === 'blocked').length;
  let status = 'resolved';
  let reason = 'completed';
  if (failures.length > 0) {
    status = 'error';
    reason = `${failures.length} target(s) failed`;
  } else if (blocked > 0) {
    status = 'blocked';
    reason = `${blocked} target(s) blocked`;
  } else if (enabled > 0 || alreadyEnabled > 0) {
    reason = `${enabled} enabled, ${alreadyEnabled} already enabled`;
  }

  emitAutomationReport({
    tool: 'auto-merge-enabler',
    mode: AUTO_MERGE_MODE || 'all',
    status,
    reason,
    metrics: {
      targets: prs.length,
      processed: results.length,
      enabled,
      alreadyEnabled,
      blocked,
      errors: failures.length,
    },
    data: {
      label: AUTO_MERGE_LABEL,
      results,
      failures,
    },
  });
};

await main();
