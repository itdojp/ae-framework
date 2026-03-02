const SUGGESTION_RE = /```suggestion\s*\n([\s\S]*?)```/gi;
const ACTIONABLE_PATTERNS = [
  /\b(please|must|should|need to|needs to|can you|could you)\b/i,
  /\b(add|remove|rename|replace|use|avoid|prefer|refactor|fix|update)\b/i,
  /\b(test|coverage|assert|validation|error handling|null check)\b/i,
  /(修正|変更|対応|追加|削除|置換|見直し|統一|改善|検討)\s*(してください|してほしい|必要|推奨)?/i,
];
const INFORMATIONAL_PATTERNS = [
  /\b(lgtm|looks good|nice work|thanks)\b/i,
  /問題ありません|問題なし|良さそう|このままで/i,
];

function normalizeBody(body) {
  return String(body || '')
    .replace(/\r\n/g, '\n')
    .replace(/\t/g, ' ')
    .trim();
}

function stripCodeFences(body) {
  return String(body || '').replace(/```[\s\S]*?```/g, ' ').replace(/`[^`]*`/g, ' ');
}

function toPositiveInt(raw) {
  const parsed = Number.parseInt(String(raw || '').trim(), 10);
  if (!Number.isFinite(parsed) || parsed <= 0) return null;
  return parsed;
}

function truncate(text, maxChars = 120) {
  const safeMax = Math.max(1, Number(maxChars) || 120);
  const chars = Array.from(String(text || '').trim());
  if (chars.length <= safeMax) return chars.join('');
  if (safeMax <= 3) return chars.slice(0, safeMax).join('');
  return `${chars.slice(0, safeMax - 3).join('')}...`;
}

function extractSuggestionBlocks(body) {
  const normalized = normalizeBody(body);
  SUGGESTION_RE.lastIndex = 0;
  const blocks = [];
  let match = SUGGESTION_RE.exec(normalized);
  while (match) {
    blocks.push(String(match[1] || '').replace(/\r\n/g, '\n'));
    match = SUGGESTION_RE.exec(normalized);
  }
  return blocks;
}

function isActionableText(body) {
  const normalized = normalizeBody(body);
  if (!normalized) return false;
  const stripped = stripCodeFences(normalized);
  if (!stripped.trim()) return false;
  return ACTIONABLE_PATTERNS.some((pattern) => pattern.test(stripped));
}

function isInformationalText(body) {
  const normalized = normalizeBody(body);
  if (!normalized) return true;
  const stripped = stripCodeFences(normalized);
  if (!stripped.trim()) return true;
  return INFORMATIONAL_PATTERNS.some((pattern) => pattern.test(stripped));
}

function classifyReviewCommentBody(body) {
  const normalized = normalizeBody(body);
  if (!normalized) {
    return { category: 'informational', reason: 'empty-body', normalizedBody: '' };
  }
  if (extractSuggestionBlocks(normalized).length > 0) {
    return { category: 'suggestion', reason: 'contains-suggestion-block', normalizedBody: normalized };
  }
  if (isActionableText(normalized)) {
    return { category: 'actionable', reason: 'matched-action-pattern', normalizedBody: normalized };
  }
  if (isInformationalText(normalized)) {
    return { category: 'informational', reason: 'matched-informational-pattern', normalizedBody: normalized };
  }
  return { category: 'informational', reason: 'no-action-pattern', normalizedBody: normalized };
}

function buildActionTaskFromComment(comment) {
  const body = comment?.body ?? '';
  const classification = classifyReviewCommentBody(body);
  if (classification.category !== 'actionable') return null;

  const path = String(comment?.path || '').trim();
  const line = toPositiveInt(comment?.line);
  const startCandidate = toPositiveInt(comment?.start_line) || line;
  const endCandidate = line || startCandidate;
  const startLine = startCandidate && endCandidate ? Math.min(startCandidate, endCandidate) : startCandidate;
  const endLine = startCandidate && endCandidate ? Math.max(startCandidate, endCandidate) : endCandidate;
  const commentId = toPositiveInt(comment?.id) || toPositiveInt(comment?.databaseId);
  if (!commentId) return null;
  const sourceUrl = String(comment?.html_url || comment?.url || '').trim();
  const instruction = truncate(stripCodeFences(classification.normalizedBody).replace(/\s+/g, ' '), 280);
  const titlePath = path ? `${path}${startLine ? `:${startLine}` : ''}` : 'review comment';

  return {
    source: 'review_comment',
    commentId,
    category: classification.category,
    reason: classification.reason,
    path,
    startLine,
    endLine,
    sourceUrl,
    title: `Address actionable review comment (${titlePath})`,
    instruction,
  };
}

function summarizeActionTasks(tasks, maxItems = 10) {
  const list = Array.isArray(tasks) ? tasks.filter(Boolean) : [];
  const limit = Math.max(1, Number(maxItems) || 10);
  return list.slice(0, limit).map((task, index) => {
    const location = task.path
      ? `${task.path}${task.startLine ? `:${task.startLine}` : ''}`
      : 'path-unknown';
    return `${index + 1}. comment=${task.commentId || 'n/a'} location=${location} instruction=${task.instruction}`;
  });
}

export {
  buildActionTaskFromComment,
  classifyReviewCommentBody,
  extractSuggestionBlocks,
  isActionableText,
  summarizeActionTasks,
};
