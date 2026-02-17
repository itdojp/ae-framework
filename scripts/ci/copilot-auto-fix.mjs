#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { execGh, execGhJson } from './lib/gh-exec.mjs';
import { emitAutomationReport } from './lib/automation-report.mjs';
import { sleep } from './lib/timing.mjs';
import {
  collectNonDocs,
  hasLabel,
  isActorAllowed,
  isDocsPath,
  normalizeLabelNames,
  parseActorCsv,
  toActorSet,
} from './lib/automation-guards.mjs';

const repo = process.env.GITHUB_REPOSITORY;
const prNumberRaw = process.env.PR_NUMBER ? String(process.env.PR_NUMBER).trim() : '';
const prHeadRef = process.env.PR_HEAD_REF ? String(process.env.PR_HEAD_REF).trim() : '';
const prHeadSha = process.env.PR_HEAD_SHA ? String(process.env.PR_HEAD_SHA).trim() : '';
const scope = String(process.env.AE_COPILOT_AUTO_FIX_SCOPE || 'docs').toLowerCase();
const optInLabel = String(process.env.AE_COPILOT_AUTO_FIX_LABEL || '').trim();
const actor = String(process.env.GITHUB_ACTOR || '').trim();
const forceApply = String(process.env.AE_COPILOT_AUTO_FIX_FORCE || '').trim() === '1';
const autoFixEnabled = String(process.env.AE_COPILOT_AUTO_FIX || '').trim() === '1';
const globalDisabled = String(process.env.AE_AUTOMATION_GLOBAL_DISABLE || '').trim() === '1';
const copilotActors = parseActorCsv(
  process.env.COPILOT_ACTORS,
  'github-copilot,github-copilot[bot]',
);
const copilotActorSet = toActorSet(copilotActors);

if (!repo) {
  console.error('[copilot-auto-fix] GITHUB_REPOSITORY is required.');
  emitAutomationReport({
    tool: 'copilot-auto-fix',
    mode: scope,
    status: 'error',
    reason: 'GITHUB_REPOSITORY is required',
  });
  process.exit(1);
}
if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(repo)) {
  console.error('[copilot-auto-fix] GITHUB_REPOSITORY format is invalid.');
  emitAutomationReport({
    tool: 'copilot-auto-fix',
    mode: scope,
    status: 'error',
    reason: 'GITHUB_REPOSITORY format is invalid',
  });
  process.exit(1);
}
if (!/^[1-9][0-9]*$/.test(prNumberRaw)) {
  console.error('[copilot-auto-fix] PR_NUMBER is required and must be a positive integer.');
  emitAutomationReport({
    tool: 'copilot-auto-fix',
    mode: scope,
    status: 'error',
    reason: 'PR_NUMBER is required and must be a positive integer',
  });
  process.exit(1);
}
const prNumber = Number(prNumberRaw);

const emitReport = (status, reason, extra = {}) =>
  emitAutomationReport({
    tool: 'copilot-auto-fix',
    mode: scope,
    status,
    reason,
    prNumber,
    ...extra,
  });

if (globalDisabled) {
  console.log('[copilot-auto-fix] Skip: AE_AUTOMATION_GLOBAL_DISABLE is enabled.');
  emitReport('skip', 'AE_AUTOMATION_GLOBAL_DISABLE is enabled');
  process.exit(0);
}

if (!forceApply && !autoFixEnabled) {
  console.log('[copilot-auto-fix] Skip: AE_COPILOT_AUTO_FIX is disabled after config resolution.');
  emitReport('skip', 'AE_COPILOT_AUTO_FIX is disabled after config resolution');
  process.exit(0);
}

if (!forceApply && !isActorAllowed(actor, copilotActorSet)) {
  console.log(`[copilot-auto-fix] Skip: actor ${actor || '(empty)'} is not in COPILOT_ACTORS.`);
  emitReport('skip', `actor ${actor || '(empty)'} is not in COPILOT_ACTORS`);
  process.exit(0);
}

const marker = '<!-- AE-COPILOT-AUTO-FIX v1 -->';

const execJson = (args, input) => {
  try {
    return execGhJson(args, { input });
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
      `repos/${repo}/issues/${number}/comments?per_page=100&page=${page}`,
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
    execGh(['api', '--method', 'PATCH', `repos/${repo}/issues/comments/${existing.id}`, '--input', '-'], {
      input: payload,
    });
    return;
  }
  execGh(['api', `repos/${repo}/issues/${number}/comments`, '--input', '-'], { input: payload });
};

const listPullFiles = async (number) => {
  const files = [];
  let page = 1;
  while (true) {
    const chunk = execJson([
      'api',
      `repos/${repo}/pulls/${number}/files?per_page=100&page=${page}`,
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
  return normalizeLabelNames(issue.labels);
};

const listReviewComments = async (number) => {
  const comments = [];
  let page = 1;
  while (true) {
    const chunk = execJson([
      'api',
      `repos/${repo}/pulls/${number}/comments?per_page=100&page=${page}`,
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
  const re = /```suggestion\s*\n([\s\S]*?)```/g;
  let match = null;
  while ((match = re.exec(text))) {
    let block = match[1] || '';
    block = block.replace(/\r\n/g, '\n');
    if (block.endsWith('\n')) block = block.slice(0, -1);
    blocks.push(block);
  }
  return blocks;
};

const isSubpath = (root, candidate) => candidate === root || candidate.startsWith(`${root}${path.sep}`);

const resolveSafeRepoFilePath = (repoRoot, filePath) => {
  const raw = String(filePath || '');
  if (!raw) return null;
  if (path.isAbsolute(raw)) return null;
  const normalized = path.normalize(raw);
  if (normalized === '..' || normalized.startsWith(`..${path.sep}`)) return null;
  const absolutePath = path.resolve(repoRoot, normalized);
  try {
    const repoReal = fs.realpathSync(repoRoot);
    const targetReal = fs.realpathSync(absolutePath);
    if (!isSubpath(repoReal, targetReal)) return null;
    const stat = fs.lstatSync(absolutePath);
    if (stat.isSymbolicLink()) return null;
  } catch {
    return null;
  }
  return absolutePath;
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
    if (!hasLabel(labels, optInLabel)) {
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
      emitReport('skip', `opt-in label ${optInLabel} is missing`, {
        metrics: {
          applied: 0,
          alreadyApplied: 0,
          resolvedThreads: 0,
        },
      });
      return;
    }
  }

  if (scope === 'docs') {
    const files = await listPullFiles(prNumber);
    const nonDocs = collectNonDocs(
      files
        .map((f) => f && f.filename)
        .filter((name) => typeof name === 'string'),
    );
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
      emitReport('skip', 'docs scope rejected non-doc files', {
        metrics: {
          applied: 0,
          alreadyApplied: 0,
          resolvedThreads: 0,
        },
        data: {
          nonDocSample: nonDocs.slice(0, 5),
        },
      });
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
    emitReport('skip', `unknown scope=${scope}`, {
      metrics: {
        applied: 0,
        alreadyApplied: 0,
        resolvedThreads: 0,
      },
    });
    return;
  }

  if (prHeadSha) {
    const checkedOutSha = execFileSync('git', ['rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
    if (checkedOutSha && checkedOutSha !== prHeadSha) {
      upsertComment(
        prNumber,
        formatSummary({
          appliedCount: 0,
          alreadyCount: 0,
          resolvedThreads: 0,
          changedFiles: [],
          skipped: [],
          note: `PR_HEAD_SHA mismatch; expected=${prHeadSha} actual=${checkedOutSha}. Skipping to avoid applying suggestions to the wrong commit.`,
        })
      );
      emitReport('skip', 'PR_HEAD_SHA mismatch', {
        data: {
          expectedHeadSha: prHeadSha,
          actualHeadSha: checkedOutSha,
        },
      });
      return;
    }

    const prView = execJson(['api', `repos/${repo}/pulls/${prNumber}`]);
    const currentHeadSha = prView && prView.head && prView.head.sha ? String(prView.head.sha) : '';
    if (currentHeadSha && currentHeadSha !== prHeadSha) {
      upsertComment(
        prNumber,
        formatSummary({
          appliedCount: 0,
          alreadyCount: 0,
          resolvedThreads: 0,
          changedFiles: [],
          skipped: [],
          note: `PR head advanced after review event; expected=${prHeadSha} current=${currentHeadSha}. Skipping to avoid line-number misapplication.`,
        })
      );
      emitReport('skip', 'PR head advanced after review event', {
        data: {
          expectedHeadSha: prHeadSha,
          currentHeadSha,
        },
      });
      return;
    }
  }

  const reviewComments = await listReviewComments(prNumber);
  const copilotReviewComments = reviewComments.filter(
    (c) => c && c.user && copilotActorSet.has(String(c.user.login || '').toLowerCase())
  );

  const ops = [];
  const skipped = [];

  for (const c of copilotReviewComments) {
    const commentId = c && c.id;
    const filePath = c && c.path;
    const line = c && c.line;
    const startLine = c && c.start_line;
    const commentCommitId = c && c.commit_id ? String(c.commit_id) : '';
    if (!commentId || !filePath || !Number.isFinite(line)) {
      skipped.push(`comment=${commentId || 'unknown'}: missing path/line`);
      continue;
    }
    if (prHeadSha && !commentCommitId) {
      skipped.push(`comment=${commentId} path=${filePath}: missing commit_id; skipping`);
      continue;
    }
    if (prHeadSha && commentCommitId && commentCommitId !== prHeadSha) {
      skipped.push(`comment=${commentId} path=${filePath}: commit_id mismatch; skipping`);
      continue;
    }
    if (scope === 'docs' && !isDocsPath(filePath)) {
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
    const absolutePath = resolveSafeRepoFilePath(repoRoot, filePath);
    if (!absolutePath) {
      skipped.push(`path=${filePath}: invalid or unsafe path`);
      continue;
    }
    const original = fs.readFileSync(absolutePath, 'utf8');
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

    const next = lines.join('\n');
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
      const copilotComments = comments.filter(
        (c) => c?.author?.login && copilotActorSet.has(String(c.author.login).toLowerCase())
      );
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

  const finalStatus = appliedCount > 0 || alreadyCount > 0 ? 'resolved' : 'skip';
  emitReport(finalStatus, finalStatus === 'resolved' ? 'suggestions processed' : 'no applicable suggestions', {
    metrics: {
      applied: appliedCount,
      alreadyApplied: alreadyCount,
      resolvedThreads,
      changedFiles: changedFiles.length,
      skipped: skipped.length,
    },
  });
};

try {
  await main();
} catch (error) {
  const message = error && error.message ? error.message : String(error);
  emitReport('error', message);
  throw error;
}
