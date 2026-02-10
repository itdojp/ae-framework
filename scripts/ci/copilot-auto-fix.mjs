#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

const repo = process.env.GITHUB_REPOSITORY;
const prNumberRaw = process.env.PR_NUMBER ? String(process.env.PR_NUMBER).trim() : '';
const prHeadRef = process.env.PR_HEAD_REF ? String(process.env.PR_HEAD_REF).trim() : '';
const scope = String(process.env.AE_COPILOT_AUTO_FIX_SCOPE || 'docs').toLowerCase();
const optInLabel = String(process.env.AE_COPILOT_AUTO_FIX_LABEL || '').trim();
const actor = String(process.env.GITHUB_ACTOR || '').trim();
const copilotActors = (process.env.COPILOT_ACTORS || 'github-copilot,github-copilot[bot]')
  .split(',')
  .map((s) => s.trim())
  .filter(Boolean);

if (!repo) {
  console.error('[copilot-auto-fix] GITHUB_REPOSITORY is required.');
  process.exit(1);
}
if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repo)) {
  console.error('[copilot-auto-fix] GITHUB_REPOSITORY format is invalid.');
  process.exit(1);
}
if (!/^[1-9][0-9]*$/.test(prNumberRaw)) {
  console.error('[copilot-auto-fix] PR_NUMBER is required and must be a positive integer.');
  process.exit(1);
}
const prNumber = Number(prNumberRaw);

if (!copilotActors.includes(actor)) {
  console.log(`[copilot-auto-fix] Skip: actor ${actor || '(empty)'} is not in COPILOT_ACTORS.`);
  process.exit(0);
}

const marker = '<!-- AE-COPILOT-AUTO-FIX v1 -->';
const docsAllowlist = [/^docs\//, /^README\.md$/];

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

const execJson = (args, input) => {
  try {
    const output = execFileSync('gh', args, {
      encoding: 'utf8',
      stdio: ['pipe', 'pipe', 'pipe'],
      input,
    });
    return JSON.parse(output);
  } catch (error) {
    const message = error && error.message ? error.message : String(error);
    console.error('[copilot-auto-fix] gh failed:', message);
    throw error;
  }
};

const listComments = (number) => {
  const comments = [];
  let page = 1;
  while (true) {
    const chunk = execJson([
      'api',
      `repos/${repo}/issues/${number}/comments`,
      '-F',
      'per_page=100',
      '-F',
      `page=${page}`,
    ]);
    if (!Array.isArray(chunk) || chunk.length === 0) break;
    comments.push(...chunk);
    if (chunk.length < 100) break;
    page += 1;
  }
  return comments;
};

const upsertComment = (number, body) => {
  const comments = listComments(number);
  const existing = comments.find(
    (comment) => comment.body && typeof comment.body === 'string' && comment.body.startsWith(marker)
  );
  const payload = JSON.stringify({ body });
  if (existing) {
    execFileSync(
      'gh',
      ['api', '--method', 'PATCH', `repos/${repo}/issues/comments/${existing.id}`, '--input', '-'],
      { stdio: ['pipe', 'inherit', 'inherit'], input: payload }
    );
    return;
  }
  execFileSync('gh', ['api', `repos/${repo}/issues/${number}/comments`, '--input', '-'], {
    stdio: ['pipe', 'inherit', 'inherit'],
    input: payload,
  });
};

const isDocPath = (filePath) => docsAllowlist.some((re) => re.test(filePath));

const listPullFiles = async (number) => {
  const files = [];
  let page = 1;
  while (true) {
    const chunk = execJson([
      'api',
      `repos/${repo}/pulls/${number}/files`,
      '-F',
      'per_page=100',
      '-F',
      `page=${page}`,
    ]);
    if (!Array.isArray(chunk) || chunk.length === 0) break;
    files.push(...chunk);
    if (chunk.length < 100) break;
    page += 1;
    await sleep(100);
  }
  return files;
};

const fetchIssueLabels = (number) => {
  const issue = execJson(['api', `repos/${repo}/issues/${number}`]);
  const labels = Array.isArray(issue.labels)
    ? issue.labels.map((l) => (typeof l === 'string' ? l : l && l.name)).filter(Boolean)
    : [];
  return labels;
};

const listReviewComments = async (number) => {
  const comments = [];
  let page = 1;
  while (true) {
    const chunk = execJson([
      'api',
      `repos/${repo}/pulls/${number}/comments`,
      '-F',
      'per_page=100',
      '-F',
      `page=${page}`,
    ]);
    if (!Array.isArray(chunk) || chunk.length === 0) break;
    comments.push(...chunk);
    if (chunk.length < 100) break;
    page += 1;
    await sleep(100);
  }
  return comments;
};

const extractSuggestionBlocks = (body) => {
  const blocks = [];
  const text = String(body || '');
  const re = /```suggestion\\s*\\n([\\s\\S]*?)```/g;
  let match = null;
  while ((match = re.exec(text))) {
    let block = match[1] || '';
    block = block.replace(/\\r\\n/g, '\\n');
    if (block.endsWith('\\n')) block = block.slice(0, -1);
    blocks.push(block);
  }
  return blocks;
};

const safeJoinRepoPath = (repoRoot, filePath) => {
  const normalized = String(filePath || '');
  if (!normalized || normalized.includes('..') || path.isAbsolute(normalized)) return null;
  return path.join(repoRoot, normalized);
};

const formatSummary = (summary) => {
  const lines = [
    marker,
    `## Copilot Auto Fix (${new Date().toISOString()})`,
    `- PR: #${prNumber}`,
    `- actor: ${actor}`,
    `- scope: ${scope}`,
  ];
  if (optInLabel) {
    lines.push(`- opt-in label: ${optInLabel}`);
  }
  lines.push(`- applied: ${summary.appliedCount} (already: ${summary.alreadyCount})`);
  lines.push(`- resolved threads: ${summary.resolvedThreads}`);
  if (summary.changedFiles.length > 0) {
    lines.push(`- changed files: ${summary.changedFiles.join(', ')}`);
  }
  if (summary.skipped.length > 0) {
    lines.push(`- skipped: ${summary.skipped.length}`);
    for (const item of summary.skipped.slice(0, 10)) {
      lines.push(`  - ${item}`);
    }
    if (summary.skipped.length > 10) {
      lines.push(`  - ... and ${summary.skipped.length - 10} more`);
    }
  }
  if (summary.note) {
    lines.push(`- note: ${summary.note}`);
  }
  return `${lines.join('\\n')}\\n`;
};

const graphqlQuery = async (query, variables) => {
  const args = ['api', 'graphql', '-f', `query=${query}`];
  for (const [key, value] of Object.entries(variables || {})) {
    // gh api graphql requires numeric variables (Int) via -F, not -f (string coercion).
    if (key === 'number' && /^[0-9]+$/.test(String(value))) {
      args.push('-F', `${key}=${value}`);
      continue;
    }
    args.push('-f', `${key}=${value}`);
  }
  return execJson(args);
};

const resolveReviewThread = async (threadId) => {
  const mutation = `mutation($threadId:ID!) {\n  resolveReviewThread(input:{threadId:$threadId}) { thread { id isResolved } }\n}`;
  return graphqlQuery(mutation, { threadId });
};

const main = async () => {
  if (optInLabel) {
    const labels = fetchIssueLabels(prNumber);
    if (!labels.includes(optInLabel)) {
      upsertComment(
        prNumber,
        formatSummary({
          appliedCount: 0,
          alreadyCount: 0,
          resolvedThreads: 0,
          changedFiles: [],
          skipped: [],
          note: `opt-in label ${optInLabel} is missing; skipping.`,
        })
      );
      return;
    }
  }

  if (scope === 'docs') {
    const files = await listPullFiles(prNumber);
    const nonDocs = files
      .map((f) => f && f.filename)
      .filter((name) => typeof name === 'string')
      .filter((name) => !isDocPath(name));
    if (nonDocs.length > 0) {
      upsertComment(
        prNumber,
        formatSummary({
          appliedCount: 0,
          alreadyCount: 0,
          resolvedThreads: 0,
          changedFiles: [],
          skipped: [],
          note: `AE_COPILOT_AUTO_FIX_SCOPE=docs: PR includes non-doc files; skipping. sample=${nonDocs.slice(0, 5).join(', ')}`,
        })
      );
      return;
    }
  } else if (scope !== 'all') {
    upsertComment(
      prNumber,
      formatSummary({
        appliedCount: 0,
        alreadyCount: 0,
        resolvedThreads: 0,
        changedFiles: [],
        skipped: [],
        note: `unknown scope=${scope}; skipping.`,
      })
    );
    return;
  }

  const reviewComments = await listReviewComments(prNumber);
  const copilotReviewComments = reviewComments.filter(
    (c) => c && c.user && copilotActors.includes(String(c.user.login || ''))
  );

  const ops = [];
  const skipped = [];

  for (const c of copilotReviewComments) {
    const commentId = c && c.id;
    const filePath = c && c.path;
    const line = c && c.line;
    const startLine = c && c.start_line;
    if (!commentId || !filePath || !Number.isFinite(line)) {
      skipped.push(`comment=${commentId || 'unknown'}: missing path/line`);
      continue;
    }
    if (scope === 'docs' && !isDocPath(filePath)) {
      skipped.push(`comment=${commentId} path=${filePath}: outside docs scope`);
      continue;
    }

    const suggestions = extractSuggestionBlocks(c.body);
    if (suggestions.length === 0) {
      skipped.push(`comment=${commentId} path=${filePath}: no suggestion block`);
      continue;
    }
    if (suggestions.length > 1) {
      skipped.push(`comment=${commentId} path=${filePath}: multiple suggestions; applying the first only`);
    }

    const start = Number.isFinite(startLine) ? startLine : line;
    const end = line;
    const minLine = Math.min(start, end);
    const maxLine = Math.max(start, end);

    ops.push({
      commentId,
      filePath,
      startLine: minLine,
      endLine: maxLine,
      suggestion: suggestions[0],
    });
  }

  const repoRoot = process.cwd();
  const opsByFile = new Map();
  for (const op of ops) {
    if (!opsByFile.has(op.filePath)) opsByFile.set(op.filePath, []);
    opsByFile.get(op.filePath).push(op);
  }

  const handledCommentIds = new Set();
  let appliedCount = 0;
  let alreadyCount = 0;

  for (const [filePath, fileOps] of opsByFile.entries()) {
    const absolutePath = safeJoinRepoPath(repoRoot, filePath);
    if (!absolutePath) {
      skipped.push(`path=${filePath}: invalid path`);
      continue;
    }
    if (!fs.existsSync(absolutePath)) {
      skipped.push(`path=${filePath}: file not found`);
      continue;
    }
    const original = fs.readFileSync(absolutePath, 'utf8');
    const hadFinalNewline = original.endsWith('\n');
    const lines = original.split('\n');

    // Apply from bottom to top to keep line numbers stable.
    fileOps.sort((a, b) => b.startLine - a.startLine || b.endLine - a.endLine);
    const appliedRanges = [];
    for (const op of fileOps) {
      const startIndex = op.startLine - 1;
      const endIndex = op.endLine - 1;
      if (startIndex < 0 || endIndex < 0 || startIndex >= lines.length || endIndex >= lines.length) {
        skipped.push(`comment=${op.commentId} path=${filePath}: line out of range (${op.startLine}-${op.endLine})`);
        continue;
      }
      if (appliedRanges.some((r) => !(op.endLine < r.start || op.startLine > r.end))) {
        skipped.push(`comment=${op.commentId} path=${filePath}: overlapping suggestions`);
        continue;
      }

      const suggestionLines = String(op.suggestion).split('\n');
      const current = lines.slice(startIndex, endIndex + 1);
      const isAlready = current.length === suggestionLines.length && current.every((v, i) => v === suggestionLines[i]);

      if (isAlready) {
        alreadyCount += 1;
        handledCommentIds.add(op.commentId);
        appliedRanges.push({ start: op.startLine, end: op.endLine });
        continue;
      }

      lines.splice(startIndex, endIndex - startIndex + 1, ...suggestionLines);
      appliedCount += 1;
      handledCommentIds.add(op.commentId);
      appliedRanges.push({ start: op.startLine, end: op.endLine });
    }

    let next = lines.join('\n');
    if (hadFinalNewline) next += '\n';
    if (next !== original) {
      fs.writeFileSync(absolutePath, next, 'utf8');
    }
  }

  const changedFiles = execFileSync('git', ['diff', '--name-only'], { encoding: 'utf8' })
    .split('\n')
    .map((s) => s.trim())
    .filter(Boolean);

  if (changedFiles.length > 0) {
    execFileSync('git', ['config', 'user.name', 'github-actions[bot]']);
    execFileSync('git', ['config', 'user.email', '41898282+github-actions[bot]@users.noreply.github.com']);
    execFileSync('git', ['add', ...changedFiles], { stdio: 'inherit' });
    execFileSync('git', ['commit', '-m', `chore(copilot): apply suggestions (#${prNumber})`], { stdio: 'inherit' });
    if (prHeadRef) {
      execFileSync('git', ['push', 'origin', `HEAD:${prHeadRef}`], { stdio: 'inherit' });
    } else {
      execFileSync('git', ['push'], { stdio: 'inherit' });
    }
  }

  // Resolve threads where all Copilot comments were handled (applied or already-applied).
  const [owner, name] = repo.split('/');
  let resolvedThreads = 0;
  try {
    const query = `query($owner:String!, $repo:String!, $number:Int!) {\n  repository(owner:$owner, name:$repo) {\n    pullRequest(number:$number) {\n      reviewThreads(first: 100) {\n        nodes {\n          id\n          isResolved\n          comments(first: 100) {\n            nodes {\n              author { login }\n              databaseId\n            }\n          }\n        }\n      }\n    }\n  }\n}`;
    const data = await graphqlQuery(query, { owner, repo: name, number: prNumber });
    const threads = data?.data?.repository?.pullRequest?.reviewThreads?.nodes || [];
    for (const thread of threads) {
      const comments = thread?.comments?.nodes || [];
      const copilotComments = comments.filter((c) => c?.author?.login && copilotActors.includes(c.author.login));
      if (copilotComments.length === 0) continue;
      const allHandled = copilotComments.every((c) => handledCommentIds.has(Number(c.databaseId)));
      if (!allHandled) continue;
      if (thread.isResolved) continue;
      await resolveReviewThread(thread.id);
      resolvedThreads += 1;
      await sleep(150);
    }
  } catch (error) {
    const message = error && error.message ? error.message : String(error);
    skipped.push(`thread resolve failed: ${message}`);
  }

  upsertComment(
    prNumber,
    formatSummary({
      appliedCount,
      alreadyCount,
      resolvedThreads,
      changedFiles,
      skipped,
      note:
        handledCommentIds.size === 0
          ? 'No Copilot suggestion blocks were applied; unresolved threads may remain.'
          : null,
    })
  );
};

await main();
