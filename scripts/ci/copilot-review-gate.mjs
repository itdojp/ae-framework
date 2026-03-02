#!/usr/bin/env node

import fs from 'node:fs';
import { execGh, execGhJson } from './lib/gh-exec.mjs';
import {
  COPILOT_REVIEW_MAX_ATTEMPTS_DEFAULT,
  COPILOT_REVIEW_WAIT_MINUTES_DEFAULT,
} from './lib/automation-defaults.mjs';
import { isActorAllowed, resolveReviewActors, toActorSet } from './lib/automation-guards.mjs';
import { readIntEnv, waitForNextRound } from './lib/round-control.mjs';

const marker = '<!-- copilot-review-gate -->';

function toPositiveInt(raw) {
  const parsed = Number.parseInt(String(raw || '').trim(), 10);
  if (!Number.isFinite(parsed) || parsed <= 0) return null;
  return parsed;
}

function readEventPayload(filePath) {
  const path = String(filePath || '').trim();
  if (!path) return {};
  try {
    const text = fs.readFileSync(path, 'utf8');
    return JSON.parse(text);
  } catch {
    return {};
  }
}

function resolvePrContext({ eventName, eventPayload, explicitPrNumber, githubRef }) {
  const number = explicitPrNumber
    || toPositiveInt(eventPayload?.pull_request?.number)
    || toPositiveInt(eventPayload?.issue?.number)
    || toPositiveInt(eventPayload?.inputs?.pr_number);
  const defaultBranch = String(eventPayload?.repository?.default_branch || '').trim();
  const isDefaultBranch = Boolean(defaultBranch) && githubRef === `refs/heads/${defaultBranch}`;
  const isIssueCommentWithoutPr = eventName === 'issue_comment' && !eventPayload?.issue?.pull_request;
  return {
    number,
    defaultBranch,
    isDefaultBranch,
    isIssueCommentWithoutPr,
  };
}

function truncateUnicodeSafe(text, maxChars) {
  const normalized = String(text || '').replace(/\s+/g, ' ').trim();
  const chars = Array.from(normalized);
  const safeMax = Number.isFinite(maxChars) ? Math.max(0, Math.trunc(maxChars)) : 0;
  if (safeMax <= 0) return '';
  if (chars.length <= safeMax) return normalized;
  if (safeMax <= 3) return chars.slice(0, safeMax).join('');
  return `${chars.slice(0, safeMax - 3).join('')}...`;
}

function resolveGateResult(pr, actorSet) {
  const reviews = Array.isArray(pr?.reviews?.nodes) ? pr.reviews.nodes : [];
  const reviewAuthors = reviews
    .map((review) => review?.author?.login)
    .filter(Boolean);
  const hasReview = reviewAuthors.some((login) => isActorAllowed(login, actorSet));

  const reviewThreads = Array.isArray(pr?.reviewThreads?.nodes) ? pr.reviewThreads.nodes : [];
  const actorThreads = reviewThreads.filter((thread) => {
    const comments = Array.isArray(thread?.comments?.nodes) ? thread.comments.nodes : [];
    return comments.some((comment) => isActorAllowed(comment?.author?.login, actorSet));
  });
  const unresolvedThreads = actorThreads.filter((thread) => !thread?.isResolved);
  const unresolvedSummaries = unresolvedThreads.slice(0, 5).map((thread, index) => {
    const comments = Array.isArray(thread?.comments?.nodes) ? thread.comments.nodes : [];
    const actorComment = comments.find((comment) => isActorAllowed(comment?.author?.login, actorSet));
    const snippet = truncateUnicodeSafe(actorComment?.bodyText || '', 140);
    return `- Thread ${index + 1}: ${snippet || '(no comment body)'}`;
  });

  return {
    hasReview,
    actorThreadsCount: actorThreads.length,
    unresolvedThreadsCount: unresolvedThreads.length,
    unresolvedSummaries,
  };
}

function execJson(args, input) {
  return execGhJson(args, { input });
}

function execText(args, input) {
  return execGh(args, { input });
}

function listComments(repo, issueNumber) {
  const comments = [];
  let page = 1;
  while (true) {
    const chunk = execJson(['api', `repos/${repo}/issues/${issueNumber}/comments?per_page=100&page=${page}`]);
    if (!Array.isArray(chunk) || chunk.length === 0) break;
    comments.push(...chunk);
    if (chunk.length < 100) break;
    page += 1;
  }
  return comments;
}

function upsertComment(repo, issueNumber, body) {
  const decoratedBody = `${body}\n\n${marker}`;
  const comments = listComments(repo, issueNumber);
  const existing = comments.find((comment) =>
    comment?.user?.login === 'github-actions[bot]'
    && typeof comment.body === 'string'
    && comment.body.includes(marker)
  );
  const payload = JSON.stringify({ body: decoratedBody });
  if (existing?.id) {
    execText(['api', '--method', 'PATCH', `repos/${repo}/issues/comments/${existing.id}`, '--input', '-'], payload);
    return;
  }
  execText(['api', `repos/${repo}/issues/${issueNumber}/comments`, '--input', '-'], payload);
}

function fetchPrReviewState(repo, prNumber) {
  const query = `query($owner:String!, $repo:String!, $number:Int!) {\n  repository(owner:$owner, name:$repo) {\n    pullRequest(number:$number) {\n      isCrossRepository\n      reviews(last:50) { nodes { author { login } state } }\n      reviewThreads(first:100) {\n        nodes {\n          isResolved\n          comments(first:25) { nodes { author { login } bodyText } }\n        }\n      }\n    }\n  }\n}`;
  const [owner, repoName] = repo.split('/');
  const response = execJson([
    'api',
    'graphql',
    '-f',
    `query=${query}`,
    '-f',
    `owner=${owner}`,
    '-f',
    `repo=${repoName}`,
    '-F',
    `number=${prNumber}`,
  ]);
  return response?.data?.repository?.pullRequest || null;
}

async function main() {
  const repo = String(process.env.GITHUB_REPOSITORY || '').trim();
  if (!repo) {
    throw new Error('GITHUB_REPOSITORY is required.');
  }

  const eventName = String(process.env.GITHUB_EVENT_NAME || '').trim();
  const eventPayload = readEventPayload(process.env.GITHUB_EVENT_PATH);
  const explicitPrNumber = toPositiveInt(process.env.PR_NUMBER || '');
  const prContext = resolvePrContext({
    eventName,
    eventPayload,
    explicitPrNumber,
    githubRef: String(process.env.GITHUB_REF || '').trim(),
  });

  if (prContext.isIssueCommentWithoutPr) {
    console.log('[copilot-review-gate] Skip: issue_comment is not for a pull request.');
    return;
  }

  if (!prContext.number) {
    if (eventName === 'workflow_dispatch' && prContext.isDefaultBranch) {
      console.log('[copilot-review-gate] Skip: no PR number provided for default-branch manual run.');
      return;
    }
    throw new Error('No PR context or valid PR_NUMBER provided.');
  }

  const reviewActors = resolveReviewActors(
    process.env.AI_REVIEW_ACTORS,
    process.env.COPILOT_ACTORS,
  );
  if (reviewActors.length === 0) {
    console.log('[copilot-review-gate] Skip: AI_REVIEW_ACTORS/COPILOT_ACTORS is empty by configuration.');
    return;
  }
  const reviewActorSet = toActorSet(reviewActors);
  const waitMinutes = readIntEnv('COPILOT_REVIEW_WAIT_MINUTES', COPILOT_REVIEW_WAIT_MINUTES_DEFAULT, 0);
  const maxAttempts = readIntEnv('COPILOT_REVIEW_MAX_ATTEMPTS', COPILOT_REVIEW_MAX_ATTEMPTS_DEFAULT, 1);

  let pr = null;
  let gateResult = null;
  for (let attempt = 1; attempt <= maxAttempts; attempt += 1) {
    pr = fetchPrReviewState(repo, prContext.number);
    if (!pr) {
      throw new Error('Cannot load PR review state via GraphQL.');
    }
    gateResult = resolveGateResult(pr, reviewActorSet);
    if (gateResult.hasReview) {
      break;
    }
    if (attempt < maxAttempts) {
      if (waitMinutes > 0) {
        console.log(
          `[copilot-review-gate] No AI review found. Retrying in ${waitMinutes} minute(s) (attempt ${attempt + 1}/${maxAttempts}).`
        );
      } else {
        console.log(
          `[copilot-review-gate] No AI review found. Retrying without delay (attempt ${attempt + 1}/${maxAttempts}).`
        );
      }
      await waitForNextRound({
        round: attempt,
        maxRounds: maxAttempts,
        baseSeconds: waitMinutes * 60,
        strategy: 'fixed',
        maxSeconds: waitMinutes * 60,
      });
    }
  }

  const allowComment = eventName === 'issue_comment' ? true : !Boolean(pr?.isCrossRepository);
  const safeUpsert = (body, label) => {
    if (!allowComment) {
      console.log(`[copilot-review-gate] Skip comment (${label}): fork PR.`);
      return;
    }
    try {
      upsertComment(repo, prContext.number, body);
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      console.warn(`[copilot-review-gate] Failed to post PR comment (${label}): ${message}`);
    }
  };

  if (!gateResult?.hasReview) {
    const body = [
      '### Copilot Review Gate',
      `No AI review found after ${maxAttempts} attempt${maxAttempts === 1 ? '' : 's'} with ${waitMinutes} minute${waitMinutes === 1 ? '' : 's'} wait.`,
      `Expected reviewers: ${reviewActors.join(', ')}`,
      'Action: request AI review and re-run the gate.',
    ].join('\n');
    safeUpsert(body, 'missing-review');
    throw new Error(`No AI review found (expected reviewers: ${reviewActors.join(', ')})`);
  }

  if ((gateResult?.unresolvedThreadsCount || 0) > 0) {
    const body = [
      '### Copilot Review Gate',
      `Unresolved AI review threads: ${gateResult.unresolvedThreadsCount}.`,
      '',
      'Sample unresolved threads:',
      ...gateResult.unresolvedSummaries,
      '',
      'Action: resolve AI review threads and re-run the gate.',
    ].join('\n');
    safeUpsert(body, 'unresolved-threads');
    throw new Error(`Unresolved AI review threads: ${gateResult.unresolvedThreadsCount}`);
  }

  console.log(
    `[copilot-review-gate] AI review present. Resolved threads: ${gateResult.actorThreadsCount}.`
  );
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch((error) => {
    const message = error instanceof Error ? error.message : String(error);
    console.error(`[copilot-review-gate] ${message}`);
    process.exit(1);
  });
}

export {
  resolvePrContext,
  resolveGateResult,
  truncateUnicodeSafe,
};
