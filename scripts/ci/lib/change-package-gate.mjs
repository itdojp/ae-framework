const PR_SUMMARY_MARKER = '<!-- AE-PR-SUMMARY -->';

function normalizeTimestamp(comment) {
  const raw = comment?.created_at ?? comment?.createdAt ?? '';
  const ts = Date.parse(String(raw));
  return Number.isFinite(ts) ? ts : 0;
}

function normalizeCommentBody(comment) {
  return typeof comment?.body === 'string' ? comment.body : '';
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

function resolveChangePackageValidationStatus(comments = []) {
  if (!Array.isArray(comments) || comments.length === 0) {
    return { status: 'missing', sourceUrl: null };
  }
  const ordered = [...comments].sort((a, b) => normalizeTimestamp(a) - normalizeTimestamp(b));
  for (let index = ordered.length - 1; index >= 0; index -= 1) {
    const comment = ordered[index];
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
  parseChangePackageValidationResult,
  resolveChangePackageValidationStatus,
};
