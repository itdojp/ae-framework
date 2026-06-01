const normalizeActorLogin = (value) => String(value || '').trim().toLowerCase();

const normalizeCommentId = (value) => {
  const id = Number(value);
  return Number.isFinite(id) ? id : null;
};

export const shouldResolveAutomationOnlyThread = (thread, {
  handledCommentIds,
  reviewActorSet,
} = {}) => {
  if (!thread || thread.isResolved) return false;

  const handled = handledCommentIds instanceof Set ? handledCommentIds : new Set();
  const actors = reviewActorSet instanceof Set ? reviewActorSet : new Set();
  if (thread.comments?.pageInfo?.hasNextPage === true) return false;

  const comments = Array.isArray(thread.comments?.nodes) ? thread.comments.nodes : [];
  if (comments.length === 0) return false;

  const automationComments = [];
  for (const comment of comments) {
    const author = normalizeActorLogin(comment?.author?.login);
    if (!author || !actors.has(author)) {
      return false;
    }
    const id = normalizeCommentId(comment?.databaseId);
    if (!id) return false;
    automationComments.push(id);
  }

  return automationComments.length > 0 && automationComments.every((id) => handled.has(id));
};

export const collectResolvableReviewThreadIds = async ({
  fetchPage,
  handledCommentIds,
  reviewActorSet,
} = {}) => {
  if (typeof fetchPage !== 'function') {
    throw new Error('fetchPage is required');
  }

  const threadIds = [];
  let cursor = null;

  while (true) {
    const page = await fetchPage(cursor);
    const nodes = Array.isArray(page?.nodes) ? page.nodes : [];
    for (const thread of nodes) {
      if (thread?.id && shouldResolveAutomationOnlyThread(thread, { handledCommentIds, reviewActorSet })) {
        threadIds.push(thread.id);
      }
    }

    if (!page?.pageInfo?.hasNextPage) break;
    cursor = page.pageInfo.endCursor || null;
    if (!cursor) {
      throw new Error('review thread pagination cursor is missing');
    }
  }

  return threadIds;
};
