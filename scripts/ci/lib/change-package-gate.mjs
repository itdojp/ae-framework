const PR_SUMMARY_MARKER = '<!-- AE-PR-SUMMARY -->';
const DEFAULT_TRUSTED_SUMMARY_AUTHORS = new Set(['github-actions', 'github-actions[bot]']);
const CHANGE_PACKAGE_VALIDATION_CHECK_NAMES = new Set([
  'Change Package Validation',
  'change-package-validation',
]);

function normalizeTimestamp(comment) {
  const raw = comment?.created_at ?? comment?.createdAt ?? '';
  const ts = Date.parse(String(raw));
  return Number.isFinite(ts) ? ts : 0;
}

function normalizeCommentBody(comment) {
  return typeof comment?.body === 'string' ? comment.body : '';
}

function normalizeAuthorLogin(comment) {
  const raw = comment?.user?.login ?? comment?.author?.login ?? '';
  return String(raw).trim().toLowerCase();
}

function isTrustedSummaryAuthor(comment, trustedAuthors = DEFAULT_TRUSTED_SUMMARY_AUTHORS) {
  const login = normalizeAuthorLogin(comment);
  if (!login) return false;
  return trustedAuthors.has(login);
}

function parseChangePackageValidationResult(body) {
  const text = String(body || '');
  if (!text.includes(PR_SUMMARY_MARKER)) {
    return null;
  }
  const sectionMatch = text.match(
    /(?:^|\n)###\s*Change Package Validation\s*\n([\s\S]*?)(?:\n###\s|\n##\s|$)/i,
  );
  if (!sectionMatch) {
    return null;
  }
  const resultMatch = sectionMatch[1].match(/(?:^|\n)-\s*result:\s*([a-z]+)\s*(?:\n|$)/i);
  if (!resultMatch) {
    return null;
  }
  const value = String(resultMatch[1] || '').trim().toLowerCase();
  if (value === 'pass' || value === 'warn' || value === 'fail') {
    return value;
  }
  return null;
}

function normalizeCheckRunTimestamp(checkRun) {
  const raw = checkRun?.completedAt
    ?? checkRun?.completed_at
    ?? checkRun?.startedAt
    ?? checkRun?.started_at
    ?? '';
  const ts = Date.parse(String(raw));
  return Number.isFinite(ts) ? ts : 0;
}

function normalizeCheckRunName(checkRun) {
  return String(checkRun?.name ?? '').trim();
}

function isChangePackageValidationCheck(checkRun) {
  return CHANGE_PACKAGE_VALIDATION_CHECK_NAMES.has(normalizeCheckRunName(checkRun));
}

function checkRunSourceUrl(checkRun) {
  return typeof checkRun?.detailsUrl === 'string'
    ? checkRun.detailsUrl
    : (typeof checkRun?.details_url === 'string'
      ? checkRun.details_url
      : (typeof checkRun?.html_url === 'string'
        ? checkRun.html_url
        : (typeof checkRun?.url === 'string' ? checkRun.url : null)));
}

function mapCheckRunToChangePackageStatus(checkRun) {
  const status = String(checkRun?.status ?? '').trim().toUpperCase();
  if (status !== 'COMPLETED') {
    return 'pending';
  }

  switch (String(checkRun?.conclusion ?? '').trim().toUpperCase()) {
    case 'SUCCESS':
      return 'pass';
    case 'NEUTRAL':
      return 'warn';
    case 'FAILURE':
    case 'CANCELLED':
    case 'TIMED_OUT':
    case 'ACTION_REQUIRED':
    case 'STALE':
      return 'fail';
    default:
      return 'missing';
  }
}

function resolveChangePackageValidationStatusFromChecks(checkRuns = []) {
  if (!Array.isArray(checkRuns) || checkRuns.length === 0) {
    return { status: 'missing', sourceUrl: null };
  }

  const candidates = checkRuns.filter(isChangePackageValidationCheck);
  if (candidates.length === 0) {
    return { status: 'missing', sourceUrl: null };
  }

  const latestTimestamp = Math.max(...candidates.map(normalizeCheckRunTimestamp));
  const latestCandidates = candidates.filter(
    (candidate) => normalizeCheckRunTimestamp(candidate) === latestTimestamp,
  );
  const latestStatuses = new Set(latestCandidates.map(mapCheckRunToChangePackageStatus));
  if (latestStatuses.size > 1) {
    return { status: 'ambiguous', sourceUrl: null };
  }

  const latest = latestCandidates[latestCandidates.length - 1];
  return {
    status: mapCheckRunToChangePackageStatus(latest),
    sourceUrl: checkRunSourceUrl(latest),
  };
}

function resolveChangePackageValidationStatus(comments = []) {
  if (!Array.isArray(comments) || comments.length === 0) {
    return { status: 'missing', sourceUrl: null };
  }
  const ordered = [...comments].sort((a, b) => normalizeTimestamp(a) - normalizeTimestamp(b));
  for (let index = ordered.length - 1; index >= 0; index -= 1) {
    const comment = ordered[index];
    if (!isTrustedSummaryAuthor(comment)) continue;
    const body = normalizeCommentBody(comment);
    const parsed = parseChangePackageValidationResult(body);
    if (!parsed) continue;
    return {
      status: parsed,
      sourceUrl: typeof comment?.html_url === 'string' ? comment.html_url : (typeof comment?.url === 'string' ? comment.url : null),
    };
  }
  return { status: 'missing', sourceUrl: null };
}

export {
  CHANGE_PACKAGE_VALIDATION_CHECK_NAMES,
  isTrustedSummaryAuthor,
  parseChangePackageValidationResult,
  resolveChangePackageValidationStatus,
  resolveChangePackageValidationStatusFromChecks,
};
