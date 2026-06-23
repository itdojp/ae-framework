const UNKNOWN = 'unknown';
const NOT_COLLECTED = 'not_collected';

const FAILURE_CONCLUSIONS = new Set(['FAILURE', 'ACTION_REQUIRED', 'STARTUP_FAILURE']);
const OPERATIONAL_CONCLUSIONS = new Set(['CANCELLED', 'TIMED_OUT']);

function ensureArray(value) {
  return Array.isArray(value) ? value : [];
}

function normalizeConclusion(value) {
  return String(value ?? '').toUpperCase();
}

function normalizeStatus(value) {
  return String(value ?? '').toUpperCase();
}

function timestampMillis(entry) {
  const candidates = [entry?.completedAt, entry?.startedAt];
  for (const value of candidates) {
    if (!value) continue;
    const parsed = Date.parse(value);
    if (Number.isFinite(parsed)) return parsed;
  }
  return 0;
}

function normalizeHeadSha(entry) {
  const candidates = [
    entry?.headSha,
    entry?.headRefOid,
    entry?.commit?.oid,
    entry?.commit?.sha,
    entry?.checkSuite?.headSha,
    entry?.checkSuite?.head_commit?.id,
    entry?.checkSuite?.head_commit?.sha,
  ];
  for (const candidate of candidates) {
    const normalized = String(candidate ?? '').trim();
    if (normalized) return normalized;
  }
  return null;
}

function normalizeCheck(entry, index) {
  return {
    index,
    type: entry?.__typename ?? entry?.type ?? 'CheckRun',
    name: String(entry?.name ?? entry?.checkName ?? entry?.context ?? entry?.workflowName ?? UNKNOWN),
    workflowName: entry?.workflowName ?? null,
    status: entry?.status ?? (entry?.state ? 'COMPLETED' : null),
    conclusion: entry?.conclusion ?? entry?.state ?? null,
    startedAt: entry?.startedAt ?? null,
    completedAt: entry?.completedAt ?? null,
    detailsUrl: entry?.detailsUrl ?? entry?.targetUrl ?? entry?.url ?? null,
    headSha: normalizeHeadSha(entry),
  };
}

function compareCheckRecency(a, b) {
  const delta = timestampMillis(a) - timestampMillis(b);
  if (delta !== 0) return delta;
  return a.index - b.index;
}

function isPolicyGateCheck(check, requiredName) {
  const values = [requiredName, check?.name, check?.workflowName]
    .map((value) => String(value ?? '').toLowerCase());
  return values.some((value) => value === 'policy-gate' || value.includes('policy gate'));
}

function isFailureConclusion(conclusion) {
  return FAILURE_CONCLUSIONS.has(normalizeConclusion(conclusion));
}

function isOperationalConclusion(conclusion) {
  return OPERATIONAL_CONCLUSIONS.has(normalizeConclusion(conclusion));
}

function sameHeadStale(entry, latest, pullRequestHeadSha) {
  const entryHead = entry?.headSha ?? null;
  const latestHead = latest?.headSha ?? null;
  const targetHead = pullRequestHeadSha ?? latestHead;

  if (entryHead && targetHead) return entryHead === targetHead;
  if (entryHead && latestHead) return entryHead === latestHead;
  if (!entryHead) {
    // `gh pr view --json statusCheckRollup` is scoped to the current PR head.
    // When GitHub omits per-check head SHA, duplicate older entries in the same
    // rollup are treated as same-head stale operational notes rather than as
    // independent current failures.
    return true;
  }
  return false;
}

export function classifyLatestCheck(check, { requiredName } = {}) {
  const status = normalizeStatus(check?.status);
  const conclusion = normalizeConclusion(check?.conclusion);
  if (status && status !== 'COMPLETED') return 'pending';
  if (conclusion === 'SUCCESS') return 'success';
  if (conclusion === 'SKIPPED') return 'skipped';
  if (isOperationalConclusion(conclusion)) return 'manual_rerun_required';
  if (isFailureConclusion(conclusion)) {
    return isPolicyGateCheck(check, requiredName) ? 'policy_semantic_failure' : 'current_required_failure';
  }
  if (!conclusion) return UNKNOWN;
  return conclusion.toLowerCase();
}

export function classifyStaleAttempt(entry, { latest, pullRequestHeadSha } = {}) {
  const conclusion = normalizeConclusion(entry?.conclusion);
  let classification = null;
  if (isOperationalConclusion(conclusion)) {
    classification = 'stale_cancelled';
  } else if (isFailureConclusion(conclusion)) {
    classification = 'superseded';
  }

  if (!classification) return null;

  return {
    classification,
    sameHeadStale: sameHeadStale(entry, latest, pullRequestHeadSha),
    status: entry.status,
    conclusion: entry.conclusion,
    workflowName: entry.workflowName,
    startedAt: entry.startedAt,
    completedAt: entry.completedAt,
    detailsUrl: entry.detailsUrl,
    headSha: entry.headSha,
  };
}

function reviewDispositionFor(classification, staleAttempts) {
  if (classification === 'current_required_failure' || classification === 'policy_semantic_failure') {
    return 'blocking';
  }
  if (classification === 'manual_rerun_required' || staleAttempts.length > 0) {
    return 'operational_note';
  }
  if (classification === 'pending') return 'pending';
  if (classification === NOT_COLLECTED) return NOT_COLLECTED;
  if (classification === UNKNOWN) return UNKNOWN;
  return 'non_blocking';
}

function countWhere(values, predicate) {
  return values.filter(predicate).length;
}

function notCollectedSummary(requiredCount) {
  return {
    required_count: requiredCount,
    collected_count: 0,
    success_count: NOT_COLLECTED,
    pending_count: NOT_COLLECTED,
    current_required_failure_count: NOT_COLLECTED,
    policy_semantic_failure_count: NOT_COLLECTED,
    operational_failure_count: NOT_COLLECTED,
    manual_rerun_required_count: NOT_COLLECTED,
    stale_or_superseded_failure_count: NOT_COLLECTED,
    stale_cancelled_count: NOT_COLLECTED,
    superseded_count: NOT_COLLECTED,
    same_head_stale_count: NOT_COLLECTED,
    semantic_blocking_failure_count: NOT_COLLECTED,
    operational_note_count: NOT_COLLECTED,
  };
}

function emptyRequiredEntry(name) {
  return {
    name,
    collected: false,
    latest: null,
    classification: NOT_COLLECTED,
    review_disposition: NOT_COLLECTED,
    attempts: 0,
    stale_or_superseded_failure_count: 0,
    stale_attempts: [],
    stale_cancelled_count: 0,
    superseded_count: 0,
    same_head_stale_count: 0,
  };
}

export function classifyRequiredCheckAttempts(name, matches, { pullRequestHeadSha = null } = {}) {
  const sorted = [...ensureArray(matches)].sort(compareCheckRecency);
  const latest = sorted.at(-1) ?? null;
  if (!latest) return emptyRequiredEntry(name);

  const staleAttempts = sorted
    .slice(0, -1)
    .map((entry) => classifyStaleAttempt(entry, { latest, pullRequestHeadSha }))
    .filter(Boolean);
  const classification = classifyLatestCheck(latest, { requiredName: name });
  const staleCancelledCount = countWhere(staleAttempts, (entry) => entry.classification === 'stale_cancelled');
  const supersededCount = countWhere(staleAttempts, (entry) => entry.classification === 'superseded');
  const sameHeadStaleCount = countWhere(staleAttempts, (entry) => entry.sameHeadStale === true);

  return {
    name,
    collected: true,
    latest: {
      status: latest.status,
      conclusion: latest.conclusion,
      workflowName: latest.workflowName,
      startedAt: latest.startedAt,
      completedAt: latest.completedAt,
      detailsUrl: latest.detailsUrl,
      headSha: latest.headSha,
    },
    classification,
    review_disposition: reviewDispositionFor(classification, staleAttempts),
    attempts: sorted.length,
    stale_or_superseded_failure_count: staleAttempts.length,
    stale_attempts: staleAttempts,
    stale_cancelled_count: staleCancelledCount,
    superseded_count: supersededCount,
    same_head_stale_count: sameHeadStaleCount,
  };
}

export function summarizeRequiredCheckClassifications(required) {
  const classifications = ensureArray(required).map((entry) => entry.classification);
  const manualRerunRequiredCount = countWhere(classifications, (entry) => entry === 'manual_rerun_required');
  const currentRequiredFailureCount = countWhere(classifications, (entry) => entry === 'current_required_failure');
  const policySemanticFailureCount = countWhere(classifications, (entry) => entry === 'policy_semantic_failure');
  const staleOrSupersededFailureCount = ensureArray(required)
    .reduce((total, entry) => total + (entry.stale_or_superseded_failure_count ?? 0), 0);

  return {
    required_count: required.length,
    collected_count: required.filter((entry) => entry.collected).length,
    success_count: countWhere(classifications, (entry) => entry === 'success'),
    pending_count: countWhere(classifications, (entry) => entry === 'pending'),
    current_required_failure_count: currentRequiredFailureCount,
    policy_semantic_failure_count: policySemanticFailureCount,
    operational_failure_count: manualRerunRequiredCount,
    manual_rerun_required_count: manualRerunRequiredCount,
    stale_or_superseded_failure_count: staleOrSupersededFailureCount,
    stale_cancelled_count: required.reduce((total, entry) => total + (entry.stale_cancelled_count ?? 0), 0),
    superseded_count: required.reduce((total, entry) => total + (entry.superseded_count ?? 0), 0),
    same_head_stale_count: required.reduce((total, entry) => total + (entry.same_head_stale_count ?? 0), 0),
    semantic_blocking_failure_count: currentRequiredFailureCount + policySemanticFailureCount,
    operational_note_count: manualRerunRequiredCount + staleOrSupersededFailureCount,
  };
}

export function collectRequiredCheckClassifications(statusCheckRollup, requiredNames, { pullRequestHeadSha = null } = {}) {
  const checks = ensureArray(statusCheckRollup).map(normalizeCheck);
  const requiredCheckNames = ensureArray(requiredNames);
  if (checks.length === 0) {
    return {
      source: NOT_COLLECTED,
      required: requiredCheckNames.map(emptyRequiredEntry),
      summary: notCollectedSummary(requiredCheckNames.length),
    };
  }

  const byName = new Map();
  for (const check of checks) {
    if (!byName.has(check.name)) byName.set(check.name, []);
    byName.get(check.name).push(check);
  }

  const required = requiredCheckNames.map((name) => classifyRequiredCheckAttempts(
    name,
    byName.get(name) ?? [],
    { pullRequestHeadSha },
  ));

  return {
    source: 'statusCheckRollup',
    required,
    summary: summarizeRequiredCheckClassifications(required),
  };
}

export const CHECK_CLASSIFICATION_VOCABULARY = Object.freeze({
  latest: [
    'success',
    'skipped',
    'pending',
    'current_required_failure',
    'policy_semantic_failure',
    'manual_rerun_required',
    UNKNOWN,
  ],
  stale: ['stale_cancelled', 'superseded', 'same_head_stale'],
  reviewDisposition: ['blocking', 'operational_note', 'pending', 'non_blocking', NOT_COLLECTED, UNKNOWN],
});
