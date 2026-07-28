import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

export const GITHUB_WORK_STATE_SCHEMA_VERSION = 'github-work-state/v1';
export const DEFAULT_GITHUB_WORK_STATE_SCHEMA_PATH = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '..',
  '..',
  'schema',
  'github-work-state-v1.schema.json',
);

const SHA_PATTERN = /^[a-f0-9]{40}$/u;
const DIGEST_PATTERN = /^sha256:[a-f0-9]{64}$/u;
const SENSITIVE_FIELD_PATTERN = /(?:authorization|body(?:text)?|secret|token)/iu;

function compareStrings(left, right) {
  return left === right ? 0 : left < right ? -1 : 1;
}

function assertNonEmptyString(value, label) {
  if (typeof value !== 'string' || value.trim().length === 0) {
    throw new Error(`${label} must be a non-empty string`);
  }
  return value.trim();
}

function assertPositiveInteger(value, label) {
  if (typeof value === 'string' && !/^[1-9][0-9]*$/u.test(value)) {
    throw new Error(`${label} must be a positive integer`);
  }
  const parsed = typeof value === 'string' ? Number(value) : value;
  if (!Number.isInteger(parsed) || parsed < 1) {
    throw new Error(`${label} must be a positive integer`);
  }
  return parsed;
}

function assertGitSha(value, label) {
  const normalized = assertNonEmptyString(value, label).toLowerCase();
  if (!SHA_PATTERN.test(normalized)) {
    throw new Error(`${label} must be a 40-character lowercase Git SHA`);
  }
  return normalized;
}

export function stableStringify(value) {
  if (Array.isArray(value)) {
    return `[${value.map((entry) => stableStringify(entry)).join(',')}]`;
  }
  if (value && typeof value === 'object') {
    const entries = Object.entries(value)
      .sort(([left], [right]) => compareStrings(left, right))
      .map(([key, entry]) => `${JSON.stringify(key)}:${stableStringify(entry)}`);
    return `{${entries.join(',')}}`;
  }
  return JSON.stringify(value);
}

export function semanticSnapshotContent(snapshot) {
  const {
    generatedAt: _generatedAt,
    pagination: _pagination,
    snapshotDigest: _snapshotDigest,
    ...semanticState
  } = snapshot;
  return semanticState;
}

export function computeSnapshotDigest(snapshot) {
  const content = stableStringify(semanticSnapshotContent(snapshot));
  return `sha256:${crypto.createHash('sha256').update(content).digest('hex')}`;
}

export function collectSensitiveFieldPaths(value, currentPath = '$') {
  if (Array.isArray(value)) {
    return value.flatMap((entry, index) => collectSensitiveFieldPaths(entry, `${currentPath}[${index}]`));
  }
  if (!value || typeof value !== 'object') {
    return [];
  }
  const findings = [];
  for (const [key, entry] of Object.entries(value)) {
    const childPath = `${currentPath}.${key}`;
    if (SENSITIVE_FIELD_PATTERN.test(key)) {
      findings.push(childPath);
    }
    findings.push(...collectSensitiveFieldPaths(entry, childPath));
  }
  return findings;
}

function boundedContractError(label, message) {
  return new Error(`${label}: ${message}`.slice(0, 480));
}

function defaultPaginationNodeKey(node) {
  if (typeof node?.id === 'string' && node.id.length > 0) return `id:${node.id}`;
  if (node?.__typename === 'CheckRun' && node.databaseId !== null && node.databaseId !== undefined) {
    return `check-run:${node.databaseId}`;
  }
  if (node?.__typename === 'StatusContext') {
    return `status-context:${String(node.context ?? '')}:${String(node.commit?.oid ?? '')}`;
  }
  return `content:${crypto.createHash('sha256').update(stableStringify(node)).digest('hex')}`;
}

export async function collectPaginated(
  fetchPage,
  { label = 'collection', pageSize = 100, maxPages = 1000, nodeKey = defaultPaginationNodeKey } = {},
) {
  if (typeof fetchPage !== 'function') {
    throw boundedContractError(label, 'fetchPage must be a function');
  }
  if (!Number.isInteger(pageSize) || pageSize < 1 || pageSize > 100) {
    throw boundedContractError(label, 'pageSize must be between 1 and 100');
  }
  if (!Number.isInteger(maxPages) || maxPages < 1 || maxPages > 10_000) {
    throw boundedContractError(label, 'maxPages must be between 1 and 10000');
  }
  if (typeof nodeKey !== 'function') {
    throw boundedContractError(label, 'nodeKey must be a function');
  }

  const nodes = [];
  const seenCursors = new Set();
  const seenNodeKeys = new Set();
  const seenPageSignatures = new Set();
  let cursor = null;
  let pagesFetched = 0;
  let declaredTotal = null;

  while (true) {
    const requestCursorKey = cursor === null ? '<initial>' : cursor;
    if (seenCursors.has(requestCursorKey)) {
      throw boundedContractError(label, `pagination cursor cycle detected before page ${pagesFetched + 1}`);
    }
    seenCursors.add(requestCursorKey);
    if (pagesFetched >= maxPages) {
      throw boundedContractError(label, `pagination exceeded maximum page count ${maxPages}`);
    }
    const page = await fetchPage({ cursor, pageSize });
    pagesFetched += 1;
    if (!page || !Array.isArray(page.nodes) || !page.pageInfo) {
      throw boundedContractError(label, `page ${pagesFetched} is malformed`);
    }
    if (typeof page.pageInfo.hasNextPage !== 'boolean') {
      throw boundedContractError(label, `page ${pagesFetched} has an invalid hasNextPage value`);
    }
    if (!Number.isInteger(page.totalCount) || page.totalCount < 0) {
      throw boundedContractError(label, `page ${pagesFetched} has an invalid totalCount`);
    }
    if (declaredTotal === null) {
      declaredTotal = page.totalCount;
    } else if (declaredTotal !== page.totalCount) {
      throw boundedContractError(label, 'totalCount changed during pagination');
    }

    const pageKeys = page.nodes.map((node) => String(nodeKey(node)));
    const pageSignature = crypto.createHash('sha256').update(stableStringify(pageKeys)).digest('hex');
    if (seenPageSignatures.has(pageSignature)) {
      throw boundedContractError(label, `duplicate page detected at page ${pagesFetched}`);
    }
    seenPageSignatures.add(pageSignature);
    for (const key of pageKeys) {
      if (seenNodeKeys.has(key)) {
        throw boundedContractError(label, `duplicate node detected at page ${pagesFetched}`);
      }
      seenNodeKeys.add(key);
    }
    nodes.push(...page.nodes);
    if (nodes.length > declaredTotal) {
      throw boundedContractError(
        label,
        `captured node count exceeds declared total (${nodes.length} > ${declaredTotal})`,
      );
    }

    if (page.pageInfo.hasNextPage !== true) {
      break;
    }
    if (page.nodes.length === 0) {
      throw boundedContractError(label, `page ${pagesFetched} hasNextPage=true but yielded no new nodes`);
    }
    if (typeof page.pageInfo.endCursor !== 'string' || page.pageInfo.endCursor.length === 0) {
      throw boundedContractError(label, 'pagination reported another page without an endCursor');
    }
    if (seenCursors.has(page.pageInfo.endCursor)) {
      throw boundedContractError(label, `pagination cursor cycle detected after page ${pagesFetched}`);
    }
    cursor = page.pageInfo.endCursor;
  }

  if (nodes.length !== declaredTotal) {
    throw boundedContractError(
      label,
      `pagination incomplete: captured ${nodes.length} of ${declaredTotal}`,
    );
  }

  return {
    nodes,
    evidence: {
      pageSize,
      pagesFetched,
      totalCount: declaredTotal,
      capturedCount: nodes.length,
      complete: true,
    },
  };
}

function normalizeReviewThread(node) {
  const threadId = assertNonEmptyString(node?.id, 'review thread id');
  const topCommentId = assertNonEmptyString(node?.comments?.nodes?.[0]?.id, `review thread ${threadId} top comment id`);
  const reviewPath = node?.path === null || node?.path === undefined
    ? null
    : assertNonEmptyString(node.path, `review thread ${threadId} path`);
  if (typeof node?.isResolved !== 'boolean') {
    throw new Error(`review thread ${threadId} isResolved must be boolean`);
  }
  return {
    threadId,
    topCommentId,
    path: reviewPath,
    isResolved: node.isResolved,
  };
}

function normalizeConclusion(node) {
  if (node?.__typename === 'CheckRun') {
    if (node.status !== 'COMPLETED') {
      return 'PENDING';
    }
    return typeof node.conclusion === 'string' && node.conclusion.length > 0
      ? node.conclusion.toUpperCase()
      : 'UNKNOWN';
  }
  if (node?.__typename === 'StatusContext') {
    const state = typeof node.state === 'string' ? node.state.toUpperCase() : 'UNKNOWN';
    return state === 'EXPECTED' || state === 'PENDING' ? 'PENDING' : state;
  }
  return 'UNKNOWN';
}

function normalizeCheckNode(node) {
  if (node?.__typename === 'CheckRun') {
    return {
      name: assertNonEmptyString(node.name, 'check run name'),
      conclusion: normalizeConclusion(node),
      runId: node.databaseId === null || node.databaseId === undefined ? null : String(node.databaseId),
      headSha: assertGitSha(node.checkSuite?.commit?.oid, `check run ${node.name ?? '<unknown>'} head SHA`),
      sourceType: 'check-run',
      appId: Number.isInteger(node.checkSuite?.app?.databaseId) && node.checkSuite.app.databaseId > 0
        ? node.checkSuite.app.databaseId
        : null,
    };
  }
  if (node?.__typename === 'StatusContext') {
    return {
      name: assertNonEmptyString(node.context, 'status context name'),
      conclusion: normalizeConclusion(node),
      runId: null,
      headSha: assertGitSha(node.commit?.oid, `status context ${node.context ?? '<unknown>'} head SHA`),
      sourceType: 'status-context',
      appId: null,
    };
  }
  return null;
}

export function normalizeRequiredCheckPolicy(rawPolicy) {
  if (!rawPolicy || typeof rawPolicy !== 'object' || Array.isArray(rawPolicy)) {
    throw new Error('required check policy must be an object');
  }
  if (rawPolicy.source !== 'classic-branch-protection') {
    throw new Error('required check policy source must be classic-branch-protection');
  }
  if (typeof rawPolicy.strict !== 'boolean') {
    throw new Error('required check policy strict must be boolean');
  }
  if (!Array.isArray(rawPolicy.checks)) {
    throw new Error('required check policy checks must be an array');
  }
  const unique = new Map();
  for (const entry of rawPolicy.checks) {
    const name = assertNonEmptyString(
      typeof entry === 'string' ? entry : entry?.name ?? entry?.context,
      'required check name',
    );
    const rawAppId = typeof entry === 'string' ? null : entry?.appId ?? entry?.app_id ?? null;
    if (rawAppId !== null && (!Number.isInteger(rawAppId) || rawAppId < 1)) {
      throw new Error(`required check ${name} appId must be a positive integer or null`);
    }
    const appId = rawAppId;
    unique.set(`${name}\u0000${appId ?? ''}`, { name, appId });
  }
  return {
    source: rawPolicy.source,
    strict: rawPolicy.strict,
    checks: Array.from(unique.values()).sort(compareRequiredCheckPolicy),
  };
}

function compareRequiredCheckPolicy(left, right) {
  return compareStrings(left.name, right.name) || (left.appId ?? 0) - (right.appId ?? 0);
}

function compareReviewThreads(left, right) {
  return compareStrings(left.threadId, right.threadId);
}

function compareRequiredChecks(left, right) {
  return compareStrings(left.name, right.name)
    || compareStrings(left.sourceType, right.sourceType)
    || (left.appId ?? 0) - (right.appId ?? 0)
    || compareStrings(String(left.runId ?? ''), String(right.runId ?? ''));
}

function requiredPolicyMatches(check, policy) {
  return check.name === policy.name && (policy.appId === null || check.appId === policy.appId);
}

function buildRequiredChecks(rawCheckNodes, requiredPolicy, headSha) {
  const allChecks = rawCheckNodes
    .map(normalizeCheckNode)
    .filter(Boolean);
  const selected = [];
  for (const policy of requiredPolicy.checks) {
    const exactHeadMatches = allChecks.filter(
      (check) => requiredPolicyMatches(check, policy) && check.headSha === headSha,
    );
    if (exactHeadMatches.length === 0) {
      selected.push({
        name: policy.name,
        conclusion: 'MISSING',
        runId: null,
        headSha,
        sourceType: 'missing',
        appId: policy.appId,
      });
      continue;
    }
    selected.push(...exactHeadMatches);
  }
  return selected.sort(compareRequiredChecks);
}

function normalizeIssueLifecycle(issue, expectedNumber) {
  if (issue?.number !== expectedNumber) {
    throw new Error(`GitHub Issue #${expectedNumber} was not returned by the authority source`);
  }
  const issueState = assertNonEmptyString(issue.state, 'Issue state').toUpperCase();
  if (!['OPEN', 'CLOSED'].includes(issueState)) throw new Error(`unsupported Issue state: ${issueState}`);
  const issueStateReason = issue.stateReason === null || issue.stateReason === undefined
    ? null
    : assertNonEmptyString(issue.stateReason, 'Issue state reason').toUpperCase();
  if (issueStateReason !== null && !['COMPLETED', 'NOT_PLANNED', 'REOPENED'].includes(issueStateReason)) {
    throw new Error(`unsupported Issue state reason: ${issueStateReason}`);
  }
  return { issueState, issueStateReason };
}

function normalizePullRequestAuthority(pullRequest, expectedNumber, expectedHead) {
  if (pullRequest?.number !== expectedNumber) {
    throw new Error(`GitHub PR #${expectedNumber} was not returned by the authority source`);
  }
  const headSha = assertGitSha(pullRequest.headRefOid, 'PR head SHA');
  if (expectedHead !== null && headSha !== assertGitSha(expectedHead, 'expected head SHA')) {
    throw new Error(`stale head: expected ${expectedHead}, GitHub reports ${headSha}`);
  }
  if (typeof pullRequest.isDraft !== 'boolean') throw new Error('PR isDraft must be boolean');
  if (typeof pullRequest.merged !== 'boolean') throw new Error('PR merged must be boolean');
  const pullRequestState = assertNonEmptyString(pullRequest.state, 'PR state').toUpperCase();
  if (!['OPEN', 'CLOSED', 'MERGED'].includes(pullRequestState)) {
    throw new Error(`unsupported PR state: ${pullRequestState}`);
  }
  const mergeCommitSha = pullRequest.mergeCommit?.oid === null || pullRequest.mergeCommit?.oid === undefined
    ? null
    : assertGitSha(pullRequest.mergeCommit.oid, 'PR merge commit SHA');
  return {
    baseRef: assertNonEmptyString(pullRequest.baseRefName, 'PR base ref'),
    baseSha: assertGitSha(pullRequest.baseRefOid, 'PR base SHA'),
    headRef: assertNonEmptyString(pullRequest.headRefName, 'PR head ref'),
    headSha,
    isDraft: pullRequest.isDraft,
    mergeState: assertNonEmptyString(pullRequest.mergeStateStatus, 'PR merge state').toUpperCase(),
    pullRequestState,
    merged: pullRequest.merged,
    mergeCommitSha,
  };
}

function authorityStamp(issueLifecycle, pullRequestAuthority) {
  return stableStringify({ ...issueLifecycle, ...pullRequestAuthority });
}

async function captureGitHubWorkStatePass({
  repository,
  issueNumber,
  pullRequestNumber,
  generatedAt,
  expectedHead,
  pageSize,
  fetchIssue,
  fetchPullRequest,
  fetchReviewThreadsPage,
  fetchRequiredChecksPage,
  fetchRequiredCheckPolicy,
}) {
  const [startIssue, startPullRequest] = await Promise.all([
    fetchIssue({ repository, issueNumber }),
    fetchPullRequest({ repository, pullRequestNumber }),
  ]);
  const startIssueLifecycle = normalizeIssueLifecycle(startIssue, issueNumber);
  const startPullRequestAuthority = normalizePullRequestAuthority(
    startPullRequest,
    pullRequestNumber,
    expectedHead,
  );

  const [threadCollection, checkCollection, rawRequiredPolicy] = await Promise.all([
    collectPaginated(
      ({ cursor, pageSize: requestedPageSize }) => fetchReviewThreadsPage({
        repository,
        pullRequestNumber,
        cursor,
        pageSize: requestedPageSize,
      }),
      { label: 'reviewThreads', pageSize },
    ),
    collectPaginated(
      ({ cursor, pageSize: requestedPageSize }) => fetchRequiredChecksPage({
        repository,
        pullRequestNumber,
        headSha: startPullRequestAuthority.headSha,
        cursor,
        pageSize: requestedPageSize,
      }),
      { label: 'requiredChecks', pageSize },
    ),
    fetchRequiredCheckPolicy({ repository, baseRef: startPullRequestAuthority.baseRef }),
  ]);

  const [endIssue, endPullRequest] = await Promise.all([
    fetchIssue({ repository, issueNumber }),
    fetchPullRequest({ repository, pullRequestNumber }),
  ]);
  const endIssueLifecycle = normalizeIssueLifecycle(endIssue, issueNumber);
  const endPullRequestAuthority = normalizePullRequestAuthority(endPullRequest, pullRequestNumber, null);
  if (authorityStamp(startIssueLifecycle, startPullRequestAuthority)
      !== authorityStamp(endIssueLifecycle, endPullRequestAuthority)) {
    throw boundedContractError('authority-state-changed-during-capture', 'start/end authority stamp mismatch');
  }

  const reviewThreads = threadCollection.nodes.map(normalizeReviewThread).sort(compareReviewThreads);
  const requiredCheckPolicy = normalizeRequiredCheckPolicy(rawRequiredPolicy);
  const requiredChecks = buildRequiredChecks(
    checkCollection.nodes,
    requiredCheckPolicy,
    startPullRequestAuthority.headSha,
  );
  const snapshotWithoutDigest = {
    schemaVersion: GITHUB_WORK_STATE_SCHEMA_VERSION,
    generatedAt,
    repository,
    issueNumber,
    pullRequestNumber,
    ...startIssueLifecycle,
    ...startPullRequestAuthority,
    reviewThreads,
    requiredCheckPolicy,
    requiredChecks,
    pagination: {
      reviewThreads: threadCollection.evidence,
      requiredChecks: checkCollection.evidence,
    },
    authoritySource: 'github-api',
  };
  const snapshot = { ...snapshotWithoutDigest, snapshotDigest: computeSnapshotDigest(snapshotWithoutDigest) };
  const semanticErrors = validateSnapshotSemantics(snapshot);
  if (semanticErrors.length > 0) {
    throw new Error(`captured snapshot is invalid: ${semanticErrors.join('; ')}`);
  }
  return snapshot;
}

export async function captureGitHubWorkState({
  repository,
  issueNumber,
  pullRequestNumber,
  generatedAt,
  expectedHead = null,
  pageSize = 100,
  fetchIssue,
  fetchPullRequest,
  fetchReviewThreadsPage,
  fetchRequiredChecksPage,
  fetchRequiredCheckPolicy,
  consistencyAttempts = 3,
}) {
  const normalizedRepository = assertNonEmptyString(repository, 'repository');
  if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/u.test(normalizedRepository)) {
    throw new Error('repository must use owner/name format');
  }
  const normalizedIssueNumber = assertPositiveInteger(issueNumber, 'issueNumber');
  const normalizedPullRequestNumber = assertPositiveInteger(pullRequestNumber, 'pullRequestNumber');
  const generatedAtInput = assertNonEmptyString(generatedAt, 'generatedAt');
  const generatedAtDate = new Date(generatedAtInput);
  if (Number.isNaN(generatedAtDate.getTime())) throw new Error('generatedAt must be a valid ISO-8601 timestamp');
  const normalizedGeneratedAt = generatedAtDate.toISOString();

  if (!Number.isInteger(consistencyAttempts) || consistencyAttempts < 1 || consistencyAttempts > 10) {
    throw new Error('consistencyAttempts must be between 1 and 10');
  }
  const passOptions = {
    repository: normalizedRepository,
    issueNumber: normalizedIssueNumber,
    pullRequestNumber: normalizedPullRequestNumber,
    generatedAt: normalizedGeneratedAt,
    expectedHead,
    pageSize,
    fetchIssue,
    fetchPullRequest,
    fetchReviewThreadsPage,
    fetchRequiredChecksPage,
    fetchRequiredCheckPolicy,
  };
  for (let attempt = 1; attempt <= consistencyAttempts; attempt += 1) {
    try {
      const first = await captureGitHubWorkStatePass(passOptions);
      const second = await captureGitHubWorkStatePass(passOptions);
      if (first.snapshotDigest === second.snapshotDigest) return second;
    } catch (error) {
      if (!String(error instanceof Error ? error.message : error).includes('authority-state-changed-during-capture')) {
        throw error;
      }
    }
  }
  throw boundedContractError(
    'authority-state-changed-during-capture',
    `semantic authority did not stabilize after ${consistencyAttempts} attempts`,
  );
}

export function compileGitHubWorkStateSchema(schemaPath = DEFAULT_GITHUB_WORK_STATE_SCHEMA_PATH) {
  const schema = JSON.parse(fs.readFileSync(schemaPath, 'utf8'));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
}

function isSorted(values, compare) {
  for (let index = 1; index < values.length; index += 1) {
    if (compare(values[index - 1], values[index]) > 0) {
      return false;
    }
  }
  return true;
}

export function validateSnapshotSemantics(
  snapshot,
  { schemaPath = DEFAULT_GITHUB_WORK_STATE_SCHEMA_PATH, validateSchema = true } = {},
) {
  const errors = [];
  if (validateSchema) {
    const validate = compileGitHubWorkStateSchema(schemaPath);
    if (!validate(snapshot)) {
      errors.push(...(validate.errors ?? []).map(
        (error) => `schema ${error.instancePath || '/'} ${error.message}`,
      ));
      return errors;
    }
  }

  const sensitivePaths = collectSensitiveFieldPaths(snapshot);
  if (sensitivePaths.length > 0) {
    errors.push(`sensitive fields are forbidden: ${sensitivePaths.join(', ')}`);
  }
  if (!DIGEST_PATTERN.test(snapshot?.snapshotDigest ?? '')) {
    errors.push('snapshotDigest is malformed');
  } else if (computeSnapshotDigest(snapshot) !== snapshot.snapshotDigest) {
    errors.push('snapshotDigest does not match the semantic snapshot content');
  }

  if (snapshot?.merged === true) {
    if (snapshot.pullRequestState !== 'MERGED') errors.push('merged PR must use pullRequestState=MERGED');
    if (!SHA_PATTERN.test(snapshot.mergeCommitSha ?? '')) errors.push('merged PR must bind mergeCommitSha');
  } else {
    if (snapshot?.pullRequestState === 'MERGED') errors.push('pullRequestState=MERGED requires merged=true');
    if (snapshot?.mergeCommitSha !== null) errors.push('unmerged PR must use mergeCommitSha=null');
  }
  if (snapshot?.issueState === 'OPEN'
      && snapshot.issueStateReason !== null
      && snapshot.issueStateReason !== 'REOPENED') {
    errors.push('open Issue state reason must be null or REOPENED');
  }
  if (snapshot?.issueState === 'CLOSED'
      && !['COMPLETED', 'NOT_PLANNED'].includes(snapshot.issueStateReason)) {
    errors.push('closed Issue must state COMPLETED or NOT_PLANNED');
  }

  const threadIds = new Set();
  const topCommentIds = new Set();
  for (const thread of snapshot?.reviewThreads ?? []) {
    if (threadIds.has(thread.threadId)) errors.push(`duplicate review thread id: ${thread.threadId}`);
    if (topCommentIds.has(thread.topCommentId)) errors.push(`duplicate top comment id: ${thread.topCommentId}`);
    threadIds.add(thread.threadId);
    topCommentIds.add(thread.topCommentId);
  }
  if (!isSorted(snapshot?.reviewThreads ?? [], compareReviewThreads)) {
    errors.push('reviewThreads must be sorted by threadId');
  }

  const requiredPolicyChecks = snapshot?.requiredCheckPolicy?.checks ?? [];
  const policyKeys = new Set();
  for (const policy of requiredPolicyChecks) {
    const key = `${policy.name}\u0000${policy.appId ?? ''}`;
    if (policyKeys.has(key)) errors.push(`duplicate required check policy: ${policy.name}`);
    policyKeys.add(key);
  }
  if (!isSorted(requiredPolicyChecks, compareRequiredCheckPolicy)) {
    errors.push('requiredCheckPolicy.checks must be sorted by name and appId');
  }
  if (!isSorted(snapshot?.requiredChecks ?? [], compareRequiredChecks)) {
    errors.push('requiredChecks must be sorted canonically');
  }
  const requiredCheckIds = new Set();
  for (const check of snapshot?.requiredChecks ?? []) {
    const checkId = [
      check.name,
      check.sourceType,
      check.appId ?? '',
      check.runId ?? '',
      check.headSha,
    ].join('\u0000');
    if (requiredCheckIds.has(checkId)) errors.push(`duplicate required check record: ${check.name}`);
    requiredCheckIds.add(checkId);
    if (check.headSha !== snapshot.headSha) {
      errors.push(`required check ${check.name} is bound to wrong head ${check.headSha}`);
    }
    if (check.sourceType === 'missing') {
      if (check.conclusion !== 'MISSING' || check.runId !== null) {
        errors.push(`missing required check ${check.name} must use conclusion=MISSING and runId=null`);
      }
    } else if (check.conclusion === 'MISSING') {
      errors.push(`materialized required check ${check.name} cannot use conclusion=MISSING`);
    }
  }
  for (const policy of requiredPolicyChecks) {
    if (!(snapshot?.requiredChecks ?? []).some((check) => requiredPolicyMatches(check, policy))) {
      errors.push(`required check policy has no exact-head record: ${policy.name}`);
    }
  }
  const reviewPagination = snapshot?.pagination?.reviewThreads;
  if (reviewPagination && reviewPagination.capturedCount !== snapshot.reviewThreads.length) {
    errors.push('review thread pagination capturedCount does not match reviewThreads length');
  }
  if (reviewPagination && reviewPagination.totalCount !== reviewPagination.capturedCount) {
    errors.push('review thread pagination is incomplete');
  }
  const checkPagination = snapshot?.pagination?.requiredChecks;
  if (checkPagination && checkPagination.totalCount !== checkPagination.capturedCount) {
    errors.push('required check pagination is incomplete');
  }
  return errors;
}

export function readAndValidateGitHubWorkStateSnapshot(
  snapshotPath,
  { schemaPath = DEFAULT_GITHUB_WORK_STATE_SCHEMA_PATH } = {},
) {
  const snapshot = JSON.parse(fs.readFileSync(snapshotPath, 'utf8'));
  const errors = validateSnapshotSemantics(snapshot, { schemaPath });
  if (errors.length > 0) {
    throw new Error(`invalid GitHub work-state snapshot ${snapshotPath}: ${errors.join('; ')}`);
  }
  return snapshot;
}

export function resolveAndValidateRepositoryLocalGitHubWorkStateSnapshot(
  snapshotReference,
  {
    repoRoot = process.cwd(),
    expectedDigest = null,
    schemaPath = DEFAULT_GITHUB_WORK_STATE_SCHEMA_PATH,
  } = {},
) {
  const reference = assertNonEmptyString(snapshotReference, 'authority snapshot reference');
  if (reference.includes('\u0000')
      || path.isAbsolute(reference)
      || /^[A-Za-z]:[\\/]/u.test(reference)
      || reference.includes('\\')) {
    throw boundedContractError('authority snapshot', 'reference must be a repository-relative POSIX path');
  }
  const segments = reference.split('/');
  if (segments.some((segment) => segment === '' || segment === '.' || segment === '..' || segment === '.git')) {
    throw boundedContractError('authority snapshot', 'reference contains a forbidden path segment');
  }

  const root = fs.realpathSync(path.resolve(repoRoot));
  const candidate = path.resolve(root, ...segments);
  if (candidate === root || !candidate.startsWith(`${root}${path.sep}`)) {
    throw boundedContractError('authority snapshot', 'reference escapes the repository root');
  }
  let current = root;
  for (const segment of segments) {
    current = path.join(current, segment);
    let stat;
    try {
      stat = fs.lstatSync(current);
    } catch {
      throw boundedContractError('authority snapshot', 'referenced file does not exist');
    }
    if (stat.isSymbolicLink()) {
      throw boundedContractError('authority snapshot', 'symbolic links are forbidden');
    }
  }
  const finalStat = fs.statSync(candidate);
  if (!finalStat.isFile()) {
    throw boundedContractError('authority snapshot', 'reference must resolve to a regular file');
  }
  const realCandidate = fs.realpathSync(candidate);
  if (!realCandidate.startsWith(`${root}${path.sep}`)) {
    throw boundedContractError('authority snapshot', 'resolved file escapes the repository root');
  }

  let snapshot;
  try {
    snapshot = JSON.parse(fs.readFileSync(realCandidate, 'utf8'));
  } catch {
    throw boundedContractError('authority snapshot', 'referenced file is not valid JSON');
  }
  const errors = validateSnapshotSemantics(snapshot, { schemaPath });
  if (errors.length > 0) {
    throw boundedContractError('authority snapshot', `contract validation failed: ${errors.join('; ')}`);
  }
  if (expectedDigest !== null) {
    const normalizedExpectedDigest = assertNonEmptyString(expectedDigest, 'expected authority snapshot digest');
    if (!DIGEST_PATTERN.test(normalizedExpectedDigest)) {
      throw boundedContractError('authority snapshot', 'expected digest is malformed');
    }
    if (snapshot.snapshotDigest !== normalizedExpectedDigest) {
      throw boundedContractError('authority snapshot', 'expected digest does not match validated snapshot');
    }
  }
  return { snapshot, snapshotPath: reference };
}

function collectCheckValues(snapshot, field) {
  const values = new Map();
  for (const check of snapshot.requiredChecks) {
    const current = values.get(check.name) ?? new Set();
    current.add(String(check[field] ?? ''));
    values.set(check.name, current);
  }
  return values;
}

function setsEqual(left, right) {
  return left.size === right.size && Array.from(left).every((value) => right.has(value));
}

export function compareGitHubWorkStateSnapshots(baseline, current, { expectedHead = null } = {}) {
  const baselineErrors = validateSnapshotSemantics(baseline);
  const currentErrors = validateSnapshotSemantics(current);
  const errors = [
    ...baselineErrors.map((error) => `baseline: ${error}`),
    ...currentErrors.map((error) => `current: ${error}`),
  ];
  if (expectedHead !== null) {
    const normalizedExpectedHead = assertGitSha(expectedHead, 'expected head SHA');
    if (current?.headSha !== normalizedExpectedHead) {
      errors.push(`current: stale head ${current?.headSha ?? '<missing>'}; expected ${normalizedExpectedHead}`);
    }
  }
  if (errors.length > 0) {
    return {
      schemaVersion: 'github-work-state-comparison/v1',
      status: 'contract-invalid',
      baselineDigest: baseline?.snapshotDigest ?? null,
      currentDigest: current?.snapshotDigest ?? null,
      changes: [],
      errors,
    };
  }

  if (baseline.snapshotDigest === current.snapshotDigest) {
    return {
      schemaVersion: 'github-work-state-comparison/v1',
      status: 'no-state-change',
      baselineDigest: baseline.snapshotDigest,
      currentDigest: current.snapshotDigest,
      changes: [],
      errors: [],
    };
  }

  const changes = [];
  const add = (kind, details) => changes.push({ kind, details });
  if (baseline.repository !== current.repository
      || baseline.issueNumber !== current.issueNumber
      || baseline.pullRequestNumber !== current.pullRequestNumber) {
    add('authority-target-changed', 'repository, Issue, or PR identity changed');
  }
  if (baseline.headRef !== current.headRef || baseline.headSha !== current.headSha) {
    add('head-changed', `${baseline.headRef}@${baseline.headSha} -> ${current.headRef}@${current.headSha}`);
  }
  if (baseline.baseRef !== current.baseRef || baseline.baseSha !== current.baseSha) {
    add('base-changed', `${baseline.baseRef}@${baseline.baseSha} -> ${current.baseRef}@${current.baseSha}`);
  }
  if (baseline.issueState !== current.issueState
      || baseline.issueStateReason !== current.issueStateReason) {
    add(
      'issue-state-changed',
      `${baseline.issueState}/${baseline.issueStateReason ?? 'null'} -> ${current.issueState}/${current.issueStateReason ?? 'null'}`,
    );
  }
  if (baseline.pullRequestState !== current.pullRequestState) {
    add('pull-request-state-changed', `${baseline.pullRequestState} -> ${current.pullRequestState}`);
  }
  if (baseline.merged !== current.merged || baseline.mergeCommitSha !== current.mergeCommitSha) {
    add(
      current.merged ? 'pull-request-merged' : 'pull-request-merge-binding-changed',
      `${baseline.mergeCommitSha ?? 'unmerged'} -> ${current.mergeCommitSha ?? 'unmerged'}`,
    );
  }
  if (stableStringify(baseline.requiredCheckPolicy) !== stableStringify(current.requiredCheckPolicy)) {
    add(
      'required-check-policy-changed',
      `classic strict/check policy changed (${baseline.requiredCheckPolicy.strict} -> ${current.requiredCheckPolicy.strict})`,
    );
  }

  const baselineThreads = new Map(baseline.reviewThreads.map((thread) => [thread.threadId, thread]));
  const currentThreads = new Map(current.reviewThreads.map((thread) => [thread.threadId, thread]));
  const baselineThreadIds = new Set(baselineThreads.keys());
  const currentThreadIds = new Set(currentThreads.keys());
  if (!setsEqual(baselineThreadIds, currentThreadIds)) {
    add(
      'review-thread-set-changed',
      `thread IDs changed (${baselineThreadIds.size} -> ${currentThreadIds.size})`,
    );
  }
  for (const threadId of currentThreadIds) {
    if (!baselineThreads.has(threadId)) add('review-thread-added', threadId);
  }
  for (const threadId of baselineThreadIds) {
    if (!currentThreads.has(threadId)) add('review-thread-removed', threadId);
  }
  for (const [threadId, baselineThread] of baselineThreads) {
    const currentThread = currentThreads.get(threadId);
    if (currentThread && baselineThread.isResolved !== currentThread.isResolved) {
      add('review-thread-resolution-changed', `${threadId}: ${baselineThread.isResolved} -> ${currentThread.isResolved}`);
    }
  }

  const baselineRunIds = collectCheckValues(baseline, 'runId');
  const currentRunIds = collectCheckValues(current, 'runId');
  const checkNames = new Set([...baselineRunIds.keys(), ...currentRunIds.keys()]);
  for (const name of checkNames) {
    const before = baselineRunIds.get(name) ?? new Set();
    const after = currentRunIds.get(name) ?? new Set();
    if (!setsEqual(before, after)) {
      add('required-check-rerun', `${name}: ${Array.from(before).join(',')} -> ${Array.from(after).join(',')}`);
    }
  }
  const baselineConclusions = collectCheckValues(baseline, 'conclusion');
  const currentConclusions = collectCheckValues(current, 'conclusion');
  for (const name of new Set([...baselineConclusions.keys(), ...currentConclusions.keys()])) {
    const before = baselineConclusions.get(name) ?? new Set();
    const after = currentConclusions.get(name) ?? new Set();
    if (!setsEqual(before, after)) {
      add('required-check-state-changed', `${name}: ${Array.from(before).join(',')} -> ${Array.from(after).join(',')}`);
    }
  }
  if (baseline.isDraft !== current.isDraft || baseline.mergeState !== current.mergeState) {
    add('pull-request-readiness-changed', 'draft/mergeability state changed');
  }
  if (changes.length === 0) {
    add('authority-state-changed', 'semantic snapshot digest changed');
  }

  return {
    schemaVersion: 'github-work-state-comparison/v1',
    status: 'stale-context',
    baselineDigest: baseline.snapshotDigest,
    currentDigest: current.snapshotDigest,
    changes,
    errors: [],
  };
}
