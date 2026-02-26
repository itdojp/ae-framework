#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { execGh, execGhJson } from './lib/gh-exec.mjs';
import { normalizeLabelNames } from './lib/automation-guards.mjs';
import {
  DEFAULT_POLICY_PATH,
  collectRequiredLabels,
  getOptionalGateLabels,
  getRiskLabels,
  inferRiskLevel,
  loadRiskPolicy,
} from './lib/risk-policy.mjs';

const DEFAULT_LABEL_STYLE = {
  'risk:low': { color: '0E8A16', description: 'Low risk PR (auto-merge candidate)' },
  'risk:high': { color: 'B60205', description: 'High risk PR (approval and gate labels required)' },
  'run-security': { color: 'FBCA04', description: 'Run security scans on this PR' },
  'run-ci-extended': { color: '1D76DB', description: 'Run CI Extended suites for this PR' },
  'enforce-artifacts': { color: '5319E7', description: 'Make artifact validation strict/blocking' },
  'enforce-testing': { color: 'C2E0C6', description: 'Make testing DDD scripts strict/blocking' },
  'enforce-context-pack': { color: '0052CC', description: 'Make Context Pack quality gate strict/blocking' },
};

const OUTPUT_JSON_PATH = 'artifacts/ci/risk-labeler-summary.json';
const OUTPUT_MD_PATH = 'artifacts/ci/risk-labeler-summary.md';

function parseArgs(argv) {
  const options = {
    prNumber: null,
    policyPath: DEFAULT_POLICY_PATH,
    dryRun: false,
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
      continue;
    }
    if (value === '--dry-run') {
      options.dryRun = true;
      continue;
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
  if (!eventPath || !fs.existsSync(eventPath)) {
    return null;
  }
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

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function appendStepSummary(markdown) {
  const summaryPath = process.env.GITHUB_STEP_SUMMARY;
  if (!summaryPath) return;
  ensureDirectory(summaryPath);
  fs.appendFileSync(summaryPath, markdown);
}

function listRepositoryLabels(repo) {
  const labels = new Set();
  let page = 1;
  while (true) {
    const items = execGhJson(['api', `repos/${repo}/labels?per_page=100&page=${page}`]);
    if (!Array.isArray(items) || items.length === 0) break;
    for (const item of items) {
      const label = String(item?.name || '').trim();
      if (label) labels.add(label);
    }
    if (items.length < 100) break;
    page += 1;
  }
  return labels;
}

function createLabelIfMissing(repo, labelName, existingLabels) {
  const name = String(labelName || '').trim();
  if (!name || existingLabels.has(name)) return false;
  const style = DEFAULT_LABEL_STYLE[name] || {
    color: 'D4C5F9',
    description: 'Auto-created by risk-labeler',
  };
  const payload = JSON.stringify({
    name,
    color: style.color,
    description: style.description,
  });
  execGh(['api', '--method', 'POST', `repos/${repo}/labels`, '--input', '-'], { input: payload });
  existingLabels.add(name);
  return true;
}

function addIssueLabels(repo, prNumber, labels) {
  if (!Array.isArray(labels) || labels.length === 0) return;
  const payload = JSON.stringify({ labels });
  execGh(['api', '--method', 'POST', `repos/${repo}/issues/${prNumber}/labels`, '--input', '-'], { input: payload });
}

function removeIssueLabel(repo, prNumber, label) {
  const encoded = encodeURIComponent(label);
  execGh(['api', '--method', 'DELETE', `repos/${repo}/issues/${prNumber}/labels/${encoded}`]);
}

function buildSummaryMarkdown(report) {
  const lines = [
    '### Risk Labeler',
    `- PR: #${report.prNumber}`,
    `- inferred risk: ${report.inferredRisk}`,
    `- current risk labels: ${report.currentRiskLabels.length > 0 ? report.currentRiskLabels.join(', ') : '(none)'}`,
    `- target labels: ${report.targetLabels.length > 0 ? report.targetLabels.join(', ') : '(none)'}`,
    `- write mode: ${report.writeMode}`,
  ];
  if (report.missingLabels.length > 0) {
    lines.push(`- labels added: ${report.missingLabels.join(', ')}`);
  }
  if (report.removedLabels.length > 0) {
    lines.push(`- labels removed: ${report.removedLabels.join(', ')}`);
  }
  if (report.writeSkips.length > 0) {
    lines.push(`- write skipped reason: ${report.writeSkips.join('; ')}`);
  }
  if (report.inference.highRiskPathMatches.length > 0) {
    lines.push(`- high-risk path matches: ${report.inference.highRiskPathMatches.slice(0, 8).join(', ')}`);
  }
  if (report.inference.forceHighRiskTriggers.length > 0) {
    const triggers = report.inference.forceHighRiskTriggers.map((item) => item.condition);
    lines.push(`- force-high triggers: ${triggers.join(', ')}`);
  }
  if (report.requiredLabels.length > 0) {
    lines.push(`- required policy labels: ${report.requiredLabels.join(', ')}`);
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
  const currentLabels = normalizeLabelNames(pullRequest?.labels || []);
  const currentLabelSet = new Set(currentLabels);

  const inference = inferRiskLevel(policy, changedFiles);
  const { requiredLabels } = collectRequiredLabels(policy, changedFiles);
  const riskLabels = getRiskLabels(policy);
  const optionalGateLabels = getOptionalGateLabels(policy);
  const desiredRisk = inference.level;

  const targetLabels = new Set([desiredRisk, ...requiredLabels]);
  const removableRiskLabel = desiredRisk === riskLabels.high ? riskLabels.low : riskLabels.high;
  const removableLabels = [];
  if (currentLabelSet.has(removableRiskLabel)) {
    removableLabels.push(removableRiskLabel);
  }

  const missingLabels = [...targetLabels].filter((label) => !currentLabelSet.has(label)).sort();
  const headRepoName = String(pullRequest?.head?.repo?.full_name || '').trim();
  const canWrite = headRepoName === repo && !options.dryRun;
  const writeSkips = [];
  let writeMode = canWrite ? 'write' : 'readonly';

  if (!canWrite) {
    if (options.dryRun) {
      writeSkips.push('dry-run');
    }
    if (headRepoName && headRepoName !== repo) {
      writeSkips.push('fork-pr');
    }
  }

  if (canWrite) {
    try {
      const repositoryLabels = listRepositoryLabels(repo);
      for (const label of [...targetLabels, ...optionalGateLabels]) {
        createLabelIfMissing(repo, label, repositoryLabels);
      }
      if (missingLabels.length > 0) {
        addIssueLabels(repo, prNumber, missingLabels);
      }
      for (const label of removableLabels) {
        removeIssueLabel(repo, prNumber, label);
      }
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      writeMode = 'readonly-fallback';
      writeSkips.push(`write-denied: ${message.replace(/\s+/g, ' ').trim()}`);
    }
  }

  const report = {
    generatedAtUtc: new Date().toISOString(),
    repository: repo,
    prNumber,
    inferredRisk: desiredRisk,
    currentRiskLabels: currentLabels.filter((label) => label === riskLabels.low || label === riskLabels.high),
    targetLabels: [...targetLabels].sort(),
    requiredLabels,
    writeMode,
    writeSkips,
    missingLabels,
    removedLabels: removableLabels,
    changedFiles,
    inference,
  };

  const markdown = buildSummaryMarkdown(report);
  persistReport(report, markdown);
  appendStepSummary(markdown);
  process.stdout.write(`${markdown}\n`);
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
    process.stderr.write(`[risk-labeler] ${message}\n`);
    process.exit(1);
  }
}

export { run };
