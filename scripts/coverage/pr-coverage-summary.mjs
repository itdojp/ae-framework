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

const HEADER = '<!-- AE-COVERAGE-SUMMARY -->\n';
const token = process.env['GITHUB_TOKEN'];
if (!token) {
  // Friendly no-op in environments without token (e.g., local runs)
  console.log('GITHUB_TOKEN not set; skipping PR coverage comment upsert');
  process.exit(0);
}

const repoFull = process.env['GITHUB_REPOSITORY'] || '';
const [owner, repo] = repoFull.split('/');
const eventName = process.env['GITHUB_EVENT_NAME'] || '';
const eventPath = process.env['GITHUB_EVENT_PATH'] || '';
const defRaw = process.env['COVERAGE_DEFAULT_THRESHOLD'];
const defTh = Number(defRaw || 80);
const hasRepoVar = typeof defRaw !== 'undefined' && defRaw !== '';
const enforceMain = (process.env['COVERAGE_ENFORCE_MAIN'] || '0') === '1';

// Load coverage summary (optional). If missing, still post a summary with n/a.
const summaryCandidates = [
  'coverage/coverage-summary.json',
  'artifacts/coverage/coverage-summary.json',
];
const summaryPath = summaryCandidates.find(p => fs.existsSync(p));
let cov = {};
let pct = 'n/a';
let pctNum = NaN;
let pctFns, pctBranches, pctStmts;
if (summaryPath) {
  try {
    cov = JSON.parse(fs.readFileSync(summaryPath, 'utf-8'));
    const ln = cov?.total?.lines?.pct;
    pctNum = typeof ln === 'number' ? ln : NaN;
    pct = typeof ln === 'number' ? fmtPct(ln) : 'n/a';
    const fnv = cov?.total?.functions?.pct;
    const brv = cov?.total?.branches?.pct;
    const stv = cov?.total?.statements?.pct;
    pctFns = typeof fnv === 'number' ? fmtPct(fnv) : fnv;
    pctBranches = typeof brv === 'number' ? fmtPct(brv) : brv;
    pctStmts = typeof stv === 'number' ? fmtPct(stv) : stv;
  } catch (e) {
    console.error('Warning: failed to parse coverage summary; proceeding with n/a');
  }
}

// Read event payload for PR number and labels
if (!fs.existsSync(eventPath)) {
  console.log('No event payload; skipping PR comment');
  process.exit(0);
}
const payload = JSON.parse(fs.readFileSync(eventPath, 'utf-8'));
const pr = payload.pull_request;
if (!pr || !owner || !repo) {
  console.log('Not a pull_request context; skipping PR comment');
  process.exit(0);
}
const number = pr.number;
const labels = (pr.labels || []).map(l => l.name);

// Threshold derivation: label override > repo var default > fallback 80
const covLabel = labels.find(n => typeof n === 'string' && n.startsWith('coverage:')) || null;
let covLabelValStr = covLabel ? String(covLabel.split(':')[1] || '').trim() : '';
const covLabelValNum = covLabelValStr !== '' ? Number(covLabelValStr) : NaN;
const hasValidLabel = isFinite(covLabelValNum);
const effNumeric = hasValidLabel ? covLabelValNum : defTh;
const effTh = fmtPct(effNumeric);

// Policy: report-only unless enforced via label or main+vars
let strict = false;
if (labels.includes('enforce-coverage')) strict = true;
if (eventName === 'push' && payload?.ref === 'refs/heads/main' && enforceMain) strict = true;
const policy = strict ? 'enforced' : 'report-only';
let rationale = 'report-only';
if (strict) {
  rationale = labels.includes('enforce-coverage')
    ? 'enforced via label: enforce-coverage'
    : 'enforced via main + repo vars (COVERAGE_ENFORCE_MAIN)';
}

const lines = [];
lines.push(`Coverage (lines): ${pct}%`);
// Include additional metrics when available (compact form)
const parts = [];
if (typeof pctFns !== 'undefined') parts.push(`functions=${pctFns}%`);
if (typeof pctBranches !== 'undefined') parts.push(`branches=${pctBranches}%`);
if (typeof pctStmts !== 'undefined') parts.push(`statements=${pctStmts}%`);
if (parts.length) lines.push(`Metrics: ${parts.join(', ')}`);
lines.push(`Threshold (effective): ${effTh}%`);
// Gate status (informational)
if (isFinite(pctNum) && isFinite(effNumeric)) {
  const ok = pctNum >= effNumeric;
  const cmp = ok ? '>=' : '<';
  const mode = ` ${strict ? '[blocking]' : '[non-blocking]'}`;
  lines.push(`Gate: ${ok ? 'OK' : 'BELOW'} (${fmtPct(pctNum)}% ${cmp} ${effTh}%)${mode}`);
}
if (covLabel) {
  if (hasValidLabel) lines.push(`- via label: ${covLabel}`);
  else lines.push(`- via label: ${covLabel} (invalid, ignored)`);
}
if (hasRepoVar) lines.push(`- repo var: COVERAGE_DEFAULT_THRESHOLD=${isFinite(defTh) ? fmtPct(defTh) : 'n/a'}%`);
lines.push(`- default: 80%`);
lines.push('Derived: label > repo var > default');
lines.push(`Policy: ${policy}`);
lines.push(`Policy source: ${rationale}`);
lines.push('Docs: docs/quality/coverage-required.md');
lines.push('Docs: docs/quality/coverage-policy.md');
lines.push('Docs: docs/ci/label-gating.md');
lines.push('Tips: /coverage <pct> to override; /enforce-coverage to enforce');
if (!summaryPath) lines.push('Note: no coverage-summary.json found (looked in coverage/ and artifacts/coverage/)');
lines.push('Reproduce: coverage → coverage/coverage-summary.json → total.lines.pct');
lines.push('Reproduce: threshold → label coverage:<pct> > vars.COVERAGE_DEFAULT_THRESHOLD > default 80');
// Report path hints (if present in workspace)
if (fs.existsSync('coverage/index.html')) {
  lines.push('Report (HTML): coverage/index.html');
}
const jsonHintPath = summaryPath || (fs.existsSync('coverage/coverage-summary.json')
  ? 'coverage/coverage-summary.json'
  : (fs.existsSync('artifacts/coverage/coverage-summary.json') ? 'artifacts/coverage/coverage-summary.json' : ''));
if (jsonHintPath) lines.push(`Report (JSON): ${jsonHintPath}`);
const body = HEADER + lines.join('\n');

// Dry-run support for local testing
const dry = process.env['AE_COVERAGE_DRY_RUN'];
if (dry === '1' || (typeof dry === 'string' && dry.toLowerCase() === 'true')) {
  console.log('AE-COVERAGE-SUMMARY (dry-run)\n' + body);
  process.exit(0);
}

// Upsert PR comment
const base = `https://api.github.com/repos/${owner}/${repo}`;
const headers = { 'authorization': `Bearer ${token}`, 'accept': 'application/vnd.github+json' };

try {
  const list = await fetch(`${base}/issues/${number}/comments?per_page=100`, { headers });
  if (!list.ok) {
    console.error('Failed to list comments', list.status, await list.text());
    process.exit(1);
  }
  const comments = await list.json();
  const mine = comments.find(c => typeof c.body === 'string' && c.body.startsWith(HEADER));
  if (mine) {
    const res = await fetch(`${base}/issues/comments/${mine.id}`, { method: 'PATCH', headers: { ...headers, 'content-type': 'application/json' }, body: JSON.stringify({ body }) });
    if (!res.ok) {
      console.error('Failed to update comment', res.status, await res.text());
      process.exit(1);
    }
    console.log('Updated AE-COVERAGE-SUMMARY');
  } else {
    const res = await fetch(`${base}/issues/${number}/comments`, { method: 'POST', headers: { ...headers, 'content-type': 'application/json' }, body: JSON.stringify({ body }) });
    if (!res.ok) {
      console.error('Failed to create comment', res.status, await res.text());
      process.exit(1);
    }
    console.log('Created AE-COVERAGE-SUMMARY');
  }
} catch (e) {
  console.error('Non-fatal: failed to upsert coverage summary comment:', e?.message || String(e));
  // Avoid failing the job due to transient network/GitHub API issues
  process.exit(0);
}
