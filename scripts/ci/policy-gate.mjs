#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import micromatch from 'micromatch';
import { execGhJson } from './lib/gh-exec.mjs';
import { normalizeLabelNames } from './lib/automation-guards.mjs';
import {
  DEFAULT_POLICY_PATH,
  collectRequiredLabels,
  getGateCheckPatternsForLabel,
  getMinHumanApprovals,
  isPolicyLabelRequirementEnabled,
  getRequiredChecks,
  getRiskLabels,
  inferRiskLevel,
  isPendingGateFailureEnabled,
  loadRiskPolicy,
} from './lib/risk-policy.mjs';

const OUTPUT_JSON_PATH = 'artifacts/ci/policy-gate-summary.json';
const OUTPUT_MD_PATH = 'artifacts/ci/policy-gate-summary.md';

function parseArgs(argv) {
  const options = {
    prNumber: null,
    policyPath: DEFAULT_POLICY_PATH,
  };
  for (let index = 2; index < argv.length; index += 1) {
    const value = argv[index];
    if ((value === '--pr' || value === '--pr-number') && argv[index + 1]) {
      options.prNumber = Number(argv[++index]);
      continue;
    }
    if (value.startsWith('--pr=')) {
      options.prNumber = Number(value.slice('--pr='.length));
      continue;
    }
    if ((value === '--policy' || value === '--policy-path') && argv[index + 1]) {
      options.policyPath = argv[++index];
      continue;
    }
    if (value.startsWith('--policy=')) {
      options.policyPath = value.slice('--policy='.length);
    }
  }
  return options;
}

function toPositiveInt(value) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) return null;
  const truncated = Math.trunc(parsed);
  if (truncated <= 0) return null;
  return truncated;
}

function readPrNumberFromEventPath(eventPath) {
  if (!eventPath || !fs.existsSync(eventPath)) return null;
  try {
    const payload = JSON.parse(fs.readFileSync(eventPath, 'utf8'));
    return toPositiveInt(
      payload?.pull_request?.number
      || payload?.workflow_run?.pull_requests?.[0]?.number
      || payload?.issue?.number
      || payload?.number
      || payload?.inputs?.pr_number,
    );
  } catch {
    return null;
  }
}

function resolvePrNumber(explicit) {
  const fromArgs = toPositiveInt(explicit);
  if (fromArgs) return fromArgs;
  const fromEnv = toPositiveInt(process.env.PR_NUMBER);
  if (fromEnv) return fromEnv;
  return readPrNumberFromEventPath(process.env.GITHUB_EVENT_PATH);
}

function fetchPullRequest(repo, prNumber) {
  return execGhJson(['api', `repos/${repo}/pulls/${prNumber}`]);
}

function fetchChangedFiles(repo, prNumber) {
  const files = [];
  let page = 1;
  while (true) {
    const items = execGhJson([
      'api',
      `repos/${repo}/pulls/${prNumber}/files?per_page=100&page=${page}`,
    ]);
    if (!Array.isArray(items) || items.length === 0) break;
    for (const item of items) {
      const filename = String(item?.filename || '').trim();
      if (filename) files.push(filename);
    }
    if (items.length < 100) break;
    page += 1;
  }
  return files.sort();
}

function fetchReviews(repo, prNumber) {
  const reviews = [];
  let page = 1;
  while (true) {
    const items = execGhJson([
      'api',
      `repos/${repo}/pulls/${prNumber}/reviews?per_page=100&page=${page}`,
    ]);
    if (!Array.isArray(items) || items.length === 0) break;
    reviews.push(...items);
    if (items.length < 100) break;
    page += 1;
  }
  return reviews;
}

function fetchStatusRollup(repo, prNumber) {
  const view = execGhJson([
    'pr',
    'view',
    String(prNumber),
    '--repo',
    repo,
    '--json',
    'statusCheckRollup',
  ]);
  return Array.isArray(view?.statusCheckRollup) ? view.statusCheckRollup : [];
}

function isHumanReviewer(review) {
  const login = String(review?.user?.login || '').trim().toLowerCase();
  const type = String(review?.user?.type || '').trim().toLowerCase();
  if (!login) return false;
  if (type === 'bot') return false;
  if (login.endsWith('[bot]')) return false;
  return true;
}

function countHumanApprovals(reviews) {
  const latestByUser = new Map();
  const sorted = Array.isArray(reviews)
    ? [...reviews].sort((a, b) => {
      const aTime = Date.parse(String(a?.submitted_at || a?.submittedAt || ''));
      const bTime = Date.parse(String(b?.submitted_at || b?.submittedAt || ''));
      if (!Number.isNaN(aTime) && !Number.isNaN(bTime) && aTime !== bTime) {
        return aTime - bTime;
      }
      return Number(a?.id || 0) - Number(b?.id || 0);
    })
    : [];
  for (const review of sorted) {
    if (!isHumanReviewer(review)) continue;
    const login = String(review?.user?.login || '').trim().toLowerCase();
    const state = String(review?.state || '').trim().toUpperCase();
    latestByUser.set(login, state);
  }
  let approvals = 0;
  for (const state of latestByUser.values()) {
    if (state === 'APPROVED') approvals += 1;
  }
  return approvals;
}

function toCheckEntries(statusRollup) {
  const entries = [];
  for (const item of statusRollup || []) {
    if (!item || typeof item !== 'object') continue;
    if (item.__typename === 'CheckRun') {
      const name = String(item.name || '').trim();
      if (!name) continue;
      const status = String(item.status || '').trim().toUpperCase();
      const conclusion = String(item.conclusion || '').trim().toUpperCase();
      let state = 'neutral';
      if (status !== 'COMPLETED') {
        state = 'pending';
      } else if (conclusion === 'SUCCESS' || conclusion === 'SKIPPED' || conclusion === 'NEUTRAL') {
        state = 'success';
      } else if (!conclusion) {
        state = 'pending';
      } else {
        state = 'failure';
      }
      entries.push({ name, state, type: 'check-run', status, conclusion });
      continue;
    }
    if (item.__typename === 'StatusContext') {
      const name = String(item.context || '').trim();
      if (!name) continue;
      const stateRaw = String(item.state || '').trim().toUpperCase();
      let state = 'neutral';
      if (stateRaw === 'SUCCESS') state = 'success';
      else if (stateRaw === 'PENDING') state = 'pending';
      else if (stateRaw === 'FAILURE' || stateRaw === 'ERROR') state = 'failure';
      entries.push({ name, state, type: 'status-context', status: stateRaw, conclusion: stateRaw });
    }
  }
  return entries;
}

function isGlobPattern(pattern) {
  return /[*?[\]{}()!+@]/.test(pattern);
}

function matchesPattern(checkName, pattern) {
  const target = String(checkName || '').trim();
  const value = String(pattern || '').trim();
  if (!target || !value) return false;
  if (isGlobPattern(value)) {
    return micromatch.isMatch(target, value, { dot: true });
  }
  return target === value;
}

function evaluateCheckRequirement(entries, patterns) {
  const patternList = Array.isArray(patterns) ? patterns.map((value) => String(value || '').trim()).filter(Boolean) : [];
  if (patternList.length === 0) {
    return {
      status: 'missing',
      matches: [],
      reason: 'no-check-pattern',
    };
  }

  const matches = entries.filter((entry) => patternList.some((pattern) => matchesPattern(entry.name, pattern)));
  if (matches.length === 0) {
    return {
      status: 'missing',
      matches: [],
      reason: 'not-found',
    };
  }
  if (matches.some((entry) => entry.state === 'failure')) {
    return {
      status: 'failure',
      matches,
      reason: 'failed',
    };
  }
  if (matches.some((entry) => entry.state === 'pending')) {
    return {
      status: 'pending',
      matches,
      reason: 'pending',
    };
  }
  return {
    status: 'success',
    matches,
    reason: 'success',
  };
}

function hasTemplateSection(body, sectionName) {
  if (!body) return false;
  const escaped = sectionName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const headingPattern = new RegExp(`^\\s*#{1,6}\\s*${escaped}(?:\\s+.*)?$`, 'im');
  if (headingPattern.test(body)) return true;
  if (/^[A-Za-z0-9_\\s]+$/.test(sectionName)) {
    const boundaryPattern = new RegExp(`(^|[^A-Za-z0-9_])${escaped}($|[^A-Za-z0-9_])`, 'i');
    return boundaryPattern.test(body);
  }
  return String(body).toLowerCase().includes(String(sectionName).toLowerCase());
}

function evaluatePolicyGate({
  policy,
  pullRequest,
  changedFiles,
  reviews,
  statusRollup,
}) {
  const errors = [];
  const warnings = [];
  const riskLabels = getRiskLabels(policy);
  const currentLabels = normalizeLabelNames(pullRequest?.labels || []);
  const currentLabelSet = new Set(currentLabels);
  const currentRiskLabels = currentLabels.filter(
    (label) => label === riskLabels.low || label === riskLabels.high,
  );

  if (currentRiskLabels.length === 0) {
    errors.push(`missing risk label: ${riskLabels.low} or ${riskLabels.high}`);
  } else if (currentRiskLabels.length > 1) {
    errors.push(`multiple risk labels: ${currentRiskLabels.join(', ')}`);
  }

  const inferred = inferRiskLevel(policy, changedFiles);
  const selectedRiskLabel = currentRiskLabels.length === 1 ? currentRiskLabels[0] : null;
  if (selectedRiskLabel && selectedRiskLabel !== inferred.level) {
    errors.push(`risk label mismatch: expected ${inferred.level}, found ${selectedRiskLabel}`);
  }

  const entries = toCheckEntries(statusRollup);
  const requiredChecks = getRequiredChecks(policy)
    .filter((value) => value !== 'policy-gate');
  const requiredCheckResults = requiredChecks.map((checkName) => ({
    checkName,
    result: evaluateCheckRequirement(entries, [checkName]),
  }));
  for (const item of requiredCheckResults) {
    if (item.result.status === 'failure') {
      errors.push(`required check failed: ${item.checkName}`);
      continue;
    }
    if (item.result.status === 'pending' || item.result.status === 'missing') {
      warnings.push(`required check not ready yet: ${item.checkName} (${item.result.status})`);
    }
  }

  const minApprovals = getMinHumanApprovals(policy);
  const approvals = countHumanApprovals(reviews);
  const { requiredLabels } = collectRequiredLabels(policy, changedFiles);
  const policyLabelsRequired = isPolicyLabelRequirementEnabled(policy);
  const missingRequiredLabels = requiredLabels.filter((label) => !currentLabelSet.has(label));

  const highRiskLabel = riskLabels.high;
  const isHighRisk = selectedRiskLabel === highRiskLabel || inferred.level === highRiskLabel;
  const gateCheckResults = [];

  if (isHighRisk) {
    if (approvals < minApprovals) {
      errors.push(`human approvals are insufficient: required ${minApprovals}, got ${approvals}`);
    }
    if (policyLabelsRequired && missingRequiredLabels.length > 0) {
      errors.push(`missing required labels: ${missingRequiredLabels.join(', ')}`);
    } else if (!policyLabelsRequired && missingRequiredLabels.length > 0) {
      warnings.push(`policy labels missing (allowed by config): ${missingRequiredLabels.join(', ')}`);
    }
    for (const label of requiredLabels) {
      if (!currentLabelSet.has(label)) continue;
      const patterns = getGateCheckPatternsForLabel(policy, label);
      const result = evaluateCheckRequirement(entries, patterns);
      gateCheckResults.push({ label, patterns, result });
      if (result.status === 'failure' || result.status === 'missing') {
        errors.push(`required gate check not green for label ${label} (${result.status})`);
      } else if (result.status === 'pending') {
        if (isPendingGateFailureEnabled(policy)) {
          errors.push(`required gate check pending for label ${label}`);
        } else {
          warnings.push(`required gate check pending for label ${label}`);
        }
      }
      if (patterns.length === 0) {
        warnings.push(`no gate_checks mapping configured for label ${label}`);
      }
    }
  }

  const body = String(pullRequest?.body || '');
  if (!hasTemplateSection(body, 'Rollback')) {
    warnings.push('PR body is missing Rollback section');
  }
  if (!hasTemplateSection(body, 'Acceptance') && !hasTemplateSection(body, '受入基準')) {
    warnings.push('PR body is missing Acceptance section');
  }

  return {
    ok: errors.length === 0,
    errors,
    warnings,
    inferredRisk: inferred,
    selectedRiskLabel,
    currentRiskLabels,
    approvals,
    minApprovals,
    requiredLabels,
    missingRequiredLabels,
    requiredCheckResults,
    gateCheckResults,
  };
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function appendStepSummary(markdown) {
  const summaryPath = process.env.GITHUB_STEP_SUMMARY;
  if (!summaryPath) return;
  ensureDirectory(summaryPath);
  fs.appendFileSync(summaryPath, markdown);
}

function buildMarkdownSummary(prNumber, evaluation) {
  const lines = [
    '### Policy Gate',
    `- PR: #${prNumber}`,
    `- result: ${evaluation.ok ? 'PASS' : 'FAIL'}`,
    `- selected risk label: ${evaluation.selectedRiskLabel || '(none)'}`,
    `- inferred risk: ${evaluation.inferredRisk.level}`,
    `- approvals: ${evaluation.approvals}/${evaluation.minApprovals}`,
  ];

  if (evaluation.requiredLabels.length > 0) {
    lines.push(`- required labels (by diff): ${evaluation.requiredLabels.join(', ')}`);
  }
  if (evaluation.missingRequiredLabels.length > 0) {
    lines.push(`- missing required labels: ${evaluation.missingRequiredLabels.join(', ')}`);
  }

  if (evaluation.requiredCheckResults.length > 0) {
    lines.push('- required checks:');
    for (const item of evaluation.requiredCheckResults) {
      lines.push(`  - ${item.checkName}: ${item.result.status}`);
    }
  }

  if (evaluation.gateCheckResults.length > 0) {
    lines.push('- gate checks (high-risk labels):');
    for (const item of evaluation.gateCheckResults) {
      lines.push(`  - ${item.label}: ${item.result.status}`);
    }
  }

  if (evaluation.errors.length > 0) {
    lines.push('- blocking errors:');
    for (const error of evaluation.errors) {
      lines.push(`  - ${error}`);
    }
  }
  if (evaluation.warnings.length > 0) {
    lines.push('- warnings:');
    for (const warning of evaluation.warnings) {
      lines.push(`  - ${warning}`);
    }
  }
  return `${lines.join('\n')}\n`;
}

function persistReport(report, markdown) {
  ensureDirectory(OUTPUT_JSON_PATH);
  fs.writeFileSync(OUTPUT_JSON_PATH, `${JSON.stringify(report, null, 2)}\n`);
  ensureDirectory(OUTPUT_MD_PATH);
  fs.writeFileSync(OUTPUT_MD_PATH, markdown);
}

async function run(options = parseArgs(process.argv)) {
  const repo = String(process.env.GITHUB_REPOSITORY || '').trim();
  if (!repo) {
    throw new Error('GITHUB_REPOSITORY is required');
  }
  const prNumber = resolvePrNumber(options.prNumber);
  if (!prNumber) {
    throw new Error('PR number is required (PR_NUMBER, --pr, or GITHUB_EVENT_PATH)');
  }

  const policy = loadRiskPolicy(options.policyPath);
  const pullRequest = fetchPullRequest(repo, prNumber);
  const changedFiles = fetchChangedFiles(repo, prNumber);
  const reviews = fetchReviews(repo, prNumber);
  const statusRollup = fetchStatusRollup(repo, prNumber);

  const evaluation = evaluatePolicyGate({
    policy,
    pullRequest,
    changedFiles,
    reviews,
    statusRollup,
  });

  const report = {
    generatedAtUtc: new Date().toISOString(),
    repository: repo,
    prNumber,
    changedFiles,
    evaluation,
  };
  const markdown = buildMarkdownSummary(prNumber, evaluation);
  persistReport(report, markdown);
  appendStepSummary(markdown);
  process.stdout.write(`${markdown}\n`);

  if (!evaluation.ok) {
    process.exitCode = 1;
  }
  return report;
}

function isDirectExecution() {
  const entry = process.argv[1];
  if (!entry) return false;
  return import.meta.url === pathToFileURL(resolve(entry)).href;
}

if (isDirectExecution()) {
  try {
    await run();
  } catch (error) {
    const message = error instanceof Error ? error.stack || error.message : String(error);
    process.stderr.write(`[policy-gate] ${message}\n`);
    process.exit(1);
  }
}

export {
  evaluateCheckRequirement,
  evaluatePolicyGate,
  run,
  toCheckEntries,
};
