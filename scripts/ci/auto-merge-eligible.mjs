#!/usr/bin/env node
import { execFileSync } from 'node:child_process';

const repo = process.env.GITHUB_REPOSITORY;
const prNumber = process.env.PR_NUMBER;
const enable = process.env.ENABLE_AUTO_MERGE === 'true';
const autoMergeMode = String(process.env.AE_AUTO_MERGE_MODE || 'all').toLowerCase();
const autoMergeLabel = String(process.env.AE_AUTO_MERGE_LABEL || '').trim();

if (!repo) {
  console.error('[auto-merge] GITHUB_REPOSITORY is required.');
  process.exit(1);
}
if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repo)) {
  console.error('[auto-merge] GITHUB_REPOSITORY format is invalid.');
  process.exit(1);
}
if (!prNumber) {
  console.error('[auto-merge] PR_NUMBER is required.');
  process.exit(1);
}
if (!/^[1-9][0-9]*$/.test(String(prNumber))) {
  console.error('[auto-merge] PR_NUMBER must be a positive integer.');
  process.exit(1);
}

const execJson = (args) => {
  try {
    const output = execFileSync('gh', args, { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
    return JSON.parse(output);
  } catch (error) {
    const message = error && error.message ? error.message : String(error);
    console.error('[auto-merge] gh failed:', message);
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
    console.error('[auto-merge] Failed to fetch branch metadata:', message);
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
    console.error('[auto-merge] Failed to fetch branch protection:', message);
    return null;
  }
};

const summarizeChecks = (rollup = [], requiredContexts = []) => {
  const counts = { success: 0, failure: 0, pending: 0, skipped: 0, neutral: 0 };
  const failed = [];
  const requiredSet = new Set(requiredContexts);
  for (const item of rollup) {
    if (item.__typename === 'CheckRun') {
      if (requiredSet.size > 0 && !requiredSet.has(item.name)) {
        continue;
      }
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
      if (requiredSet.size > 0 && !requiredSet.has(item.context)) {
        continue;
      }
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
  return { counts, failed };
};

const pr = execJson([
  'pr',
  'view',
  String(prNumber),
  '--repo',
  repo,
  '--json',
  'number,title,mergeable,reviewDecision,statusCheckRollup,baseRefName,labels',
]);

const branchMeta = fetchBranchMeta(repo, pr.baseRefName);
if (branchMeta === null) {
  console.log('[auto-merge] Not eligible (branch metadata unavailable).');
  process.exit(0);
}

const protectionSummary = fetchProtectionSummary(repo, pr.baseRefName, branchMeta);
if (protectionSummary === null) {
  console.log('[auto-merge] Not eligible (branch protection unavailable).');
  process.exit(0);
}
const { requiredContexts, reviewRequirement } = protectionSummary;
const { counts, failed } = summarizeChecks(pr.statusCheckRollup || [], requiredContexts);
const labels = Array.isArray(pr.labels) ? pr.labels.map((l) => l && l.name).filter(Boolean) : [];
const labelEligible = (() => {
  if (autoMergeMode === 'all') return true;
  if (autoMergeMode !== 'label') return false;
  if (!autoMergeLabel) return false;
  return labels.includes(autoMergeLabel);
})();
const reviewEligible = reviewRequirement.approvalRequired ? pr.reviewDecision === 'APPROVED' : true;
const eligible = pr.mergeable === 'MERGEABLE' && labelEligible && reviewEligible && counts.failure === 0 && counts.pending === 0;

console.log(`[auto-merge] PR #${pr.number}: ${pr.title}`);
console.log(`[auto-merge] mergeable=${pr.mergeable} review=${pr.reviewDecision} (required=${reviewRequirement.approvalRequired ? `yes/${reviewRequirement.requiredApprovals}` : 'no'})`);
console.log(`[auto-merge] mode=${autoMergeMode} label=${autoMergeLabel || '(none)'} hasLabel=${labels.includes(autoMergeLabel)}`);
console.log(
  `[auto-merge] required checks: ${requiredContexts.length || 'none'} | success=${counts.success} failure=${counts.failure} pending=${counts.pending}`
);
if (failed.length > 0) {
  console.log(`[auto-merge] failed: ${failed.slice(0, 10).join(', ')}`);
}

if (!eligible) {
  console.log('[auto-merge] Not eligible.');
  process.exit(0);
}

if (!enable) {
  console.log('[auto-merge] Eligible. Enable with ENABLE_AUTO_MERGE=true to activate.');
  process.exit(0);
}

execFileSync('gh', ['pr', 'merge', String(prNumber), '--repo', repo, '--auto', '--squash'], {
  stdio: 'inherit',
});
