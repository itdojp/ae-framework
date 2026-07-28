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

export async function collectPaginated(fetchPage, { label, pageSize = 100 } = {}) {
  if (typeof fetchPage !== 'function') {
    throw new Error(`${label ?? 'collection'} fetchPage must be a function`);
  }
  if (!Number.isInteger(pageSize) || pageSize < 1 || pageSize > 100) {
    throw new Error(`${label ?? 'collection'} pageSize must be between 1 and 100`);
  }

  const nodes = [];
  let cursor = null;
  let pagesFetched = 0;
  let declaredTotal = null;

  while (true) {
    const page = await fetchPage({ cursor, pageSize });
    pagesFetched += 1;
    if (!page || !Array.isArray(page.nodes) || !page.pageInfo) {
      throw new Error(`${label ?? 'collection'} page ${pagesFetched} is malformed`);
    }
    if (!Number.isInteger(page.totalCount) || page.totalCount < 0) {
      throw new Error(`${label ?? 'collection'} page ${pagesFetched} has an invalid totalCount`);
    }
    if (declaredTotal === null) {
      declaredTotal = page.totalCount;
    } else if (declaredTotal !== page.totalCount) {
      throw new Error(`${label ?? 'collection'} totalCount changed during pagination`);
    }
    nodes.push(...page.nodes);

    if (page.pageInfo.hasNextPage !== true) {
      break;
    }
    if (typeof page.pageInfo.endCursor !== 'string' || page.pageInfo.endCursor.length === 0) {
      throw new Error(`${label ?? 'collection'} pagination reported another page without an endCursor`);
    }
    if (page.pageInfo.endCursor === cursor) {
      throw new Error(`${label ?? 'collection'} pagination cursor did not advance`);
    }
    cursor = page.pageInfo.endCursor;
  }

  if (nodes.length !== declaredTotal) {
    throw new Error(
      `${label ?? 'collection'} pagination incomplete: captured ${nodes.length} of ${declaredTotal}`,
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
  const entries = Array.isArray(rawPolicy) ? rawPolicy : [];
  const unique = new Map();
  for (const entry of entries) {
    const name = assertNonEmptyString(
      typeof entry === 'string' ? entry : entry?.name ?? entry?.context,
      'required check name',
    );
    const rawAppId = typeof entry === 'string' ? null : entry?.appId ?? entry?.app_id ?? null;
    const appId = Number.isInteger(rawAppId) && rawAppId > 0 ? rawAppId : null;
    unique.set(`${name}\u0000${appId ?? ''}`, { name, appId });
  }
  return Array.from(unique.values()).sort(compareRequiredCheckPolicy);
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
  for (const policy of requiredPolicy) {
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

  const issue = await fetchIssue({ repository: normalizedRepository, issueNumber: normalizedIssueNumber });
  if (issue?.number !== normalizedIssueNumber) {
    throw new Error(`GitHub Issue #${normalizedIssueNumber} was not returned by the authority source`);
  }
  const pullRequest = await fetchPullRequest({
    repository: normalizedRepository,
    pullRequestNumber: normalizedPullRequestNumber,
  });
  if (pullRequest?.number !== normalizedPullRequestNumber) {
    throw new Error(`GitHub PR #${normalizedPullRequestNumber} was not returned by the authority source`);
  }

  const headSha = assertGitSha(pullRequest.headRefOid, 'PR head SHA');
  if (expectedHead !== null && headSha !== assertGitSha(expectedHead, 'expected head SHA')) {
    throw new Error(`stale head: expected ${expectedHead}, GitHub reports ${headSha}`);
  }
  const baseSha = assertGitSha(pullRequest.baseRefOid, 'PR base SHA');
  const mergeState = assertNonEmptyString(pullRequest.mergeStateStatus, 'PR merge state').toUpperCase();
  if (typeof pullRequest.isDraft !== 'boolean') {
    throw new Error('PR isDraft must be boolean');
  }

  const [threadCollection, checkCollection, rawRequiredPolicy] = await Promise.all([
    collectPaginated(
      ({ cursor, pageSize: requestedPageSize }) => fetchReviewThreadsPage({
        repository: normalizedRepository,
        pullRequestNumber: normalizedPullRequestNumber,
        cursor,
        pageSize: requestedPageSize,
      }),
      { label: 'reviewThreads', pageSize },
    ),
    collectPaginated(
      ({ cursor, pageSize: requestedPageSize }) => fetchRequiredChecksPage({
        repository: normalizedRepository,
        pullRequestNumber: normalizedPullRequestNumber,
        headSha,
        cursor,
        pageSize: requestedPageSize,
      }),
      { label: 'requiredChecks', pageSize },
    ),
    fetchRequiredCheckPolicy({
      repository: normalizedRepository,
      baseRef: pullRequest.baseRefName,
    }),
  ]);

  const reviewThreads = threadCollection.nodes.map(normalizeReviewThread).sort(compareReviewThreads);
  const requiredCheckPolicy = normalizeRequiredCheckPolicy(rawRequiredPolicy);
  const requiredChecks = buildRequiredChecks(checkCollection.nodes, requiredCheckPolicy, headSha);

  const snapshotWithoutDigest = {
    schemaVersion: GITHUB_WORK_STATE_SCHEMA_VERSION,
    generatedAt: normalizedGeneratedAt,
    repository: normalizedRepository,
    issueNumber: normalizedIssueNumber,
    pullRequestNumber: normalizedPullRequestNumber,
    baseRef: assertNonEmptyString(pullRequest.baseRefName, 'PR base ref'),
    baseSha,
    headRef: assertNonEmptyString(pullRequest.headRefName, 'PR head ref'),
    headSha,
    isDraft: pullRequest.isDraft,
    mergeState,
    reviewThreads,
    requiredCheckPolicy,
    requiredChecks,
    pagination: {
      reviewThreads: threadCollection.evidence,
      requiredChecks: checkCollection.evidence,
    },
    authoritySource: 'github-api',
  };
  const snapshot = {
    ...snapshotWithoutDigest,
    snapshotDigest: computeSnapshotDigest(snapshotWithoutDigest),
  };
  const semanticErrors = validateSnapshotSemantics(snapshot);
  if (semanticErrors.length > 0) {
    throw new Error(`captured snapshot is invalid: ${semanticErrors.join('; ')}`);
  }
  return snapshot;
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

  const policyKeys = new Set();
  for (const policy of snapshot?.requiredCheckPolicy ?? []) {
    const key = `${policy.name}\u0000${policy.appId ?? ''}`;
    if (policyKeys.has(key)) errors.push(`duplicate required check policy: ${policy.name}`);
    policyKeys.add(key);
  }
  if (!isSorted(snapshot?.requiredCheckPolicy ?? [], compareRequiredCheckPolicy)) {
    errors.push('requiredCheckPolicy must be sorted by name and appId');
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
  for (const policy of snapshot?.requiredCheckPolicy ?? []) {
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
    add('pull-request-state-changed', `draft/merge state changed`);
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
