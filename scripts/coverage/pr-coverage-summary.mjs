#!/usr/bin/env node
// Upsert PR comment with coverage summary under header <!-- AE-COVERAGE-SUMMARY -->
// Inputs via env:
// - GITHUB_TOKEN (required)
// - GITHUB_REPOSITORY, GITHUB_EVENT_NAME, GITHUB_EVENT_PATH
// - COVERAGE_DEFAULT_THRESHOLD (optional; default 80)
// - COVERAGE_ENFORCE_MAIN (optional; default 0)
// Mirrors logic found in coverage-check.yml, adding quick reproduce notes.

import fs from 'node:fs';

function fmtPct(v) {
  if (typeof v !== 'number' || !isFinite(v)) return String(v);
  const s = v.toFixed(1);
  return s.endsWith('.0') ? String(Math.round(v)) : s;
}

function parseNumToken(raw) {
  if (typeof raw === 'string') {
    let s = raw.trim();
    if (s.endsWith('%')) s = s.slice(0, -1).trim();
    // Collapse inner whitespace (e.g., "82 . 5" -> "82.5")
    s = s.replace(/\s+/g, '');
    const n = Number(s);
    return isFinite(n) ? n : NaN;
  }
  if (typeof raw === 'number') return isFinite(raw) ? raw : NaN;
  return NaN;
}

const HEADER = '<!-- AE-COVERAGE-SUMMARY -->\n';
const MAX_COMMENT_VALUE = 200;
const dryFlag = process.env['AE_COVERAGE_DRY_RUN'];
const isDryRun = dryFlag === '1' || (typeof dryFlag === 'string' && dryFlag.toLowerCase() === 'true');
const skipFlag = process.env['AE_COVERAGE_SKIP_COMMENT'];
const isSkip = skipFlag === '1' || (typeof skipFlag === 'string' && skipFlag.toLowerCase() === 'true');
const includePaths = process.env['AE_COVERAGE_INCLUDE_PATHS'] === '1';
if (isSkip) {
  console.log('Note: AE_COVERAGE_SKIP_COMMENT set; skipping PR coverage comment upsert');
  process.exit(0);
}
const token = process.env['GITHUB_TOKEN'];
if (!token && !isDryRun) {
  // Friendly no-op in environments without token (e.g., local runs)
  console.log('GITHUB_TOKEN not set; skipping PR coverage comment upsert');
  process.exit(0);
}

let repoFull = process.env['GITHUB_REPOSITORY'] || '';
let owner = '', repo = '';
if (repoFull.includes('/')) {
  [owner, repo] = repoFull.split('/');
}
const eventName = process.env['GITHUB_EVENT_NAME'] || '';
const eventPath = process.env['GITHUB_EVENT_PATH'] || '';
const rawRepoVar = process.env['COVERAGE_DEFAULT_THRESHOLD'];
const defTh = parseNumToken(rawRepoVar);
const hasRepoVar = typeof rawRepoVar !== 'undefined' && rawRepoVar !== '';
const repoVarIsNumeric = isFinite(defTh);
const repoVarValidRange = repoVarIsNumeric && defTh >= 0 && defTh <= 100;
const enforceMain = (process.env['COVERAGE_ENFORCE_MAIN'] || '0') === '1';
const sanitizeCommentValue = (value, fallback = 'n/a') => {
  const raw = String(value ?? '');
  const cleaned = raw.replace(/[\u0000-\u001f\u007f]/g, '').trim().slice(0, MAX_COMMENT_VALUE);
  return cleaned.length ? cleaned : fallback;
};

// Load coverage summary (optional). If missing, still post a summary with n/a.
const overrideSummary = process.env['AE_COVERAGE_SUMMARY_PATH'];
const summaryCandidates = [
  overrideSummary,
  'coverage/coverage-summary.json',
  'artifacts/coverage/coverage-summary.json',
].filter(Boolean);
const summaryPath = summaryCandidates.find(p => fs.existsSync(p));
let cov = {};
let pct = 'n/a';
let pctNum = NaN;
let pctFns, pctBranches, pctStmts;
if (summaryPath) {
  try {
    cov = JSON.parse(fs.readFileSync(summaryPath, 'utf-8'));
    const lnNum = parseNumToken(cov?.total?.lines?.pct);
    pctNum = typeof lnNum === 'number' && isFinite(lnNum) ? lnNum : NaN;
    pct = isFinite(pctNum) ? fmtPct(pctNum) : 'n/a';
    const fnNum = parseNumToken(cov?.total?.functions?.pct);
    const brNum = parseNumToken(cov?.total?.branches?.pct);
    const stNum = parseNumToken(cov?.total?.statements?.pct);
    pctFns = isFinite(fnNum) ? fmtPct(fnNum) : undefined;
    pctBranches = isFinite(brNum) ? fmtPct(brNum) : undefined;
    pctStmts = isFinite(stNum) ? fmtPct(stNum) : undefined;
  } catch (e) {
    console.error('Warning: failed to parse coverage summary; proceeding with n/a');
  }
}

// Read event payload for PR number and labels
if (!fs.existsSync(eventPath)) {
  console.log('No event payload; skipping PR comment');
  process.exit(0);
}
let payload;
try {
  payload = JSON.parse(fs.readFileSync(eventPath, 'utf-8'));
} catch (e) {
  console.log('Warning: failed to parse event payload; skipping PR comment');
  process.exit(0);
}
// Fallback owner/repo from event payload when env is missing
if (!owner || !repo) {
  const full = payload?.repository?.full_name;
  if (typeof full === 'string' && full.includes('/')) {
    [owner, repo] = full.split('/');
  } else {
    const ow = payload?.repository?.owner?.login;
    const rp = payload?.repository?.name;
    if (ow && rp) { owner = ow; repo = rp; }
  }
}
// If still not resolved, skip posting gracefully
if (!owner || !repo) {
  console.log('Note: unable to resolve repository coordinates; skipping PR coverage comment upsert');
  process.exit(0);
}
const pr = payload.pull_request;
if (!pr || !owner || !repo) {
  console.log('Not a pull_request context; skipping PR comment');
  process.exit(0);
}
const number = pr.number;
const labels = (pr.labels || [])
  .map(l => (typeof l === 'string' ? l : (l && typeof l.name === 'string' ? l.name : '')))
  .filter(Boolean);
const labelsLower = labels.map(n => (typeof n === 'string' ? n.toLowerCase() : ''));

// Threshold derivation: label override > repo var default > fallback 80
// Prefer the last coverage:<pct> label if multiple are present
const covLabel = [...labels].reverse().find(n => {
  if (typeof n !== 'string') return false;
  return /^coverage\s*:/i.test(n);
}) || null;
let covLabelValStr = covLabel ? String(covLabel.split(':')[1] || '').trim() : '';
const covLabelValNum = covLabelValStr !== '' ? parseNumToken(covLabelValStr) : NaN;
const hasValidLabel = isFinite(covLabelValNum) && covLabelValNum >= 0 && covLabelValNum <= 100;
const effNumeric = hasValidLabel
  ? covLabelValNum
  : (repoVarValidRange ? defTh : 80);
const effTh = fmtPct(effNumeric);

// Policy: report-only unless enforced via label or main+vars
let strict = false;
if (labelsLower.includes('enforce-coverage')) strict = true;
if (eventName === 'push' && payload?.ref === 'refs/heads/main' && enforceMain) strict = true;
const policy = strict ? 'enforced' : 'report-only';
let rationale = 'report-only';
if (strict) {
  rationale = labelsLower.includes('enforce-coverage')
    ? 'enforced via label: enforce-coverage'
    : 'enforced via main + repo vars (COVERAGE_ENFORCE_MAIN)';
}

const lines = [];
lines.push(`Coverage (lines): ${sanitizeCommentValue(pct)}%`);
// Include additional metrics when available (compact form)
const parts = [];
if (typeof pctFns !== 'undefined') parts.push(`functions=${sanitizeCommentValue(pctFns)}%`);
if (typeof pctBranches !== 'undefined') parts.push(`branches=${sanitizeCommentValue(pctBranches)}%`);
if (typeof pctStmts !== 'undefined') parts.push(`statements=${sanitizeCommentValue(pctStmts)}%`);
if (parts.length) lines.push(`Metrics: ${parts.join(', ')}`);
lines.push(`Threshold (effective): ${sanitizeCommentValue(effTh)}%`);
// Gate status (informational)
  if (isFinite(pctNum) && isFinite(effNumeric)) {
  const ok = pctNum >= effNumeric;
    const cmp = ok ? '>=' : '<';
    const mode = ` ${strict ? '[blocking]' : '[non-blocking]'}`;
    lines.push(`Gate: ${ok ? 'OK' : 'BELOW'} (${sanitizeCommentValue(fmtPct(pctNum))}% ${cmp} ${sanitizeCommentValue(effTh)}%)${mode}`);
    if (!ok) {
      lines.push('Action: add tests to raise coverage or adjust threshold via /coverage <pct>');
    }
  }
  if (covLabel) {
  const safeCovLabel = sanitizeCommentValue(covLabel, 'label');
  if (hasValidLabel) lines.push(`- via label: ${safeCovLabel}`);
  else lines.push(`- via label: ${safeCovLabel} (invalid, ignored)`);
}
if (hasRepoVar) {
  const valStr = repoVarIsNumeric ? `${fmtPct(defTh)}%` : 'n/a%';
  const note = repoVarValidRange ? '' : ' (invalid, ignored)';
  lines.push(`- repo var: COVERAGE_DEFAULT_THRESHOLD=${sanitizeCommentValue(valStr)}${note}`);
}
lines.push(`- default: 80%`);
lines.push('Derived: label > repo var > default');
lines.push('Rules: label override last-wins; accepts 0–100; trims %/spaces');
lines.push(`Policy: ${policy}`);
lines.push(`Policy source: ${rationale}`);
lines.push('Docs: docs/quality/coverage-required.md');
lines.push('Docs: docs/quality/coverage-policy.md');
lines.push('Docs: docs/ci/label-gating.md');
lines.push('Tips: /coverage <pct> to override; /enforce-coverage to enforce');
if (!summaryPath) {
  const msg = overrideSummary
    ? 'Note: no coverage-summary.json found (override path not found; looked in coverage/ and artifacts/coverage/)'
    : 'Note: no coverage-summary.json found (looked in coverage/ and artifacts/coverage/)';
  lines.push(msg);
}
// If summary exists but lines.pct is missing/unreadable, add a gentle note
if (summaryPath && !isFinite(pctNum)) {
  lines.push('Note: total.lines.pct not found or invalid in coverage summary');
}
lines.push('Reproduce: coverage → coverage/coverage-summary.json → total.lines.pct');
lines.push('Reproduce: threshold → label coverage:<pct> > vars.COVERAGE_DEFAULT_THRESHOLD > default 80');
// Report path hints (opt-in)
if (includePaths) {
  const htmlHintPath = fs.existsSync('coverage/index.html')
    ? 'coverage/index.html'
    : (fs.existsSync('artifacts/coverage/index.html') ? 'artifacts/coverage/index.html' : '');
  if (htmlHintPath) lines.push(`Report (HTML): ${sanitizeCommentValue(htmlHintPath, '')}`);
  const jsonHintPath = summaryPath || (fs.existsSync('coverage/coverage-summary.json')
    ? 'coverage/coverage-summary.json'
    : (fs.existsSync('artifacts/coverage/coverage-summary.json') ? 'artifacts/coverage/coverage-summary.json' : ''));
  if (jsonHintPath) lines.push(`Report (JSON): ${sanitizeCommentValue(jsonHintPath, '')}`);
}
// Threshold source line (concise) should be part of the rendered body
const src = hasValidLabel ? 'label' : (repoVarValidRange ? 'repo var' : 'default');
lines.push(`Source: ${src}`);
const body = HEADER + lines.join('\n');

// Dry-run support for local testing
if (isDryRun) {
  console.log('AE-COVERAGE-SUMMARY (dry-run)\n' + body);
  process.exit(0);
}

// Upsert PR comment
const base = `https://api.github.com/repos/${owner}/${repo}`;
const headers = { 'authorization': `Bearer ${token}`, 'accept': 'application/vnd.github+json' };

try {
  const list = await fetch(`${base}/issues/${number}/comments?per_page=100`, { headers }); // lgtm [js/file-access-to-http] CI posts a coverage summary to GitHub by design.
  if (!list.ok) {
    console.error('Non-fatal: failed to list comments', list.status, await list.text());
    process.exit(0);
  }
  const comments = await list.json();
  const mine = comments.find(c => typeof c.body === 'string' && c.body.startsWith(HEADER));
  if (mine) {
    const res = await fetch(`${base}/issues/comments/${mine.id}`, { method: 'PATCH', headers: { ...headers, 'content-type': 'application/json' }, body: JSON.stringify({ body }) }); // lgtm [js/file-access-to-http] CI updates the coverage summary comment intentionally.
    if (!res.ok) {
      console.error('Non-fatal: failed to update comment', res.status, await res.text());
      process.exit(0);
    }
    console.log('Updated AE-COVERAGE-SUMMARY');
  } else {
    const res = await fetch(`${base}/issues/${number}/comments`, { method: 'POST', headers: { ...headers, 'content-type': 'application/json' }, body: JSON.stringify({ body }) }); // lgtm [js/file-access-to-http] CI creates the coverage summary comment intentionally.
    if (!res.ok) {
      console.error('Non-fatal: failed to create comment', res.status, await res.text());
      process.exit(0);
    }
    console.log('Created AE-COVERAGE-SUMMARY');
  }
} catch (e) {
  console.error('Non-fatal: failed to upsert coverage summary comment:', e?.message || String(e));
  // Avoid failing the job due to transient network/GitHub API issues
  process.exit(0);
}
