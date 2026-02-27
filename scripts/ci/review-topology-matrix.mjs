#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';

const OUTPUT_JSON_PATH = 'artifacts/ci/review-topology-matrix.json';
const OUTPUT_MD_PATH = 'artifacts/ci/review-topology-matrix.md';
const POLICY_GATE_SUMMARY_PATH = 'artifacts/ci/policy-gate-summary.json';

function parseArgs(argv) {
  const options = {
    prNumber: null,
    repository: String(process.env.GITHUB_REPOSITORY || '').trim(),
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
    if ((value === '--repo' || value === '--repository') && argv[index + 1]) {
      options.repository = String(argv[++index] || '').trim();
      continue;
    }
    if (value.startsWith('--repo=')) {
      options.repository = String(value.slice('--repo='.length)).trim();
      continue;
    }
  }

  return options;
}

function toPositiveInt(value) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) return null;
  const truncated = Math.trunc(parsed);
  return truncated > 0 ? truncated : null;
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function removeFileIfExists(filePath) {
  if (!fs.existsSync(filePath)) {
    return;
  }
  fs.rmSync(filePath, { force: true });
}

function readPolicyGateSummary() {
  if (!fs.existsSync(POLICY_GATE_SUMMARY_PATH)) {
    return { summary: null, error: `missing ${POLICY_GATE_SUMMARY_PATH}` };
  }
  try {
    const raw = fs.readFileSync(POLICY_GATE_SUMMARY_PATH, 'utf8');
    return { summary: JSON.parse(raw), error: '' };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return { summary: null, error: `invalid JSON in ${POLICY_GATE_SUMMARY_PATH}: ${message}` };
  }
}

function runPolicyGateScenario({ scenarioId, prNumber, repository, reviewTopology, approvalOverride }) {
  const env = { ...process.env };
  env.GITHUB_REPOSITORY = repository;
  env.PR_NUMBER = String(prNumber);

  if (reviewTopology) env.AE_REVIEW_TOPOLOGY = reviewTopology;
  else delete env.AE_REVIEW_TOPOLOGY;

  const hasApprovalOverride = approvalOverride !== undefined && approvalOverride !== null && String(approvalOverride) !== '';
  if (hasApprovalOverride) env.AE_POLICY_MIN_HUMAN_APPROVALS = String(approvalOverride);
  else delete env.AE_POLICY_MIN_HUMAN_APPROVALS;

  let exitCode = 0;
  let stderr = '';
  removeFileIfExists(POLICY_GATE_SUMMARY_PATH);
  try {
    execFileSync('node', ['scripts/ci/policy-gate.mjs', '--pr', String(prNumber)], {
      env,
      stdio: ['ignore', 'ignore', 'pipe'],
    });
  } catch (error) {
    exitCode = Number(error?.status ?? 1);
    stderr = String(error?.stderr || '').trim();
  }

  const { summary, error: summaryError } = readPolicyGateSummary();
  const evaluation = summary?.evaluation || {};
  const errors = Array.isArray(evaluation.errors) ? [...evaluation.errors] : [];
  if (summaryError) {
    errors.push(`policy-gate summary unavailable: ${summaryError}`);
  }
  if (exitCode !== 0 && !stderr && errors.length === 0) {
    errors.push(`policy-gate exited with status ${exitCode}`);
  }
  return {
    scenarioId,
    reviewTopology: reviewTopology || '(default)',
    approvalOverride: approvalOverride || '',
    exitCode,
    ok: Boolean(evaluation.ok) && exitCode === 0 && !summaryError,
    selectedRiskLabel: String(evaluation.selectedRiskLabel || ''),
    inferredRisk: String(evaluation?.inferredRisk?.level || ''),
    approvals: Number(evaluation.approvals || 0),
    effectiveMinApprovals: Number(evaluation.effectiveMinApprovals ?? evaluation.minApprovals ?? 0),
    minApprovalsSource: String(evaluation.minApprovalsSource || ''),
    errors,
    warnings: Array.isArray(evaluation.warnings) ? evaluation.warnings : [],
    summaryError: summaryError || '',
    stderr,
  };
}

function buildMarkdown(report) {
  const lines = [
    '### Review Topology Matrix',
    `- generatedAtUtc: ${report.generatedAtUtc}`,
    `- repository: ${report.repository}`,
    `- prNumber: ${report.prNumber}`,
    '',
    '| Scenario | AE_REVIEW_TOPOLOGY | AE_POLICY_MIN_HUMAN_APPROVALS | Result | Approvals | Error Count |',
    '| --- | --- | --- | --- | --- | --- |',
  ];

  for (const item of report.scenarios) {
    lines.push(
      `| ${item.scenarioId} | ${item.reviewTopology} | ${item.approvalOverride || '(none)'} | ${item.ok ? 'PASS' : 'FAIL'} | ${item.approvals}/${item.effectiveMinApprovals} | ${item.errors.length} |`,
    );
  }

  lines.push('', '#### Details');
  for (const item of report.scenarios) {
    lines.push(
      `- ${item.scenarioId}: result=${item.ok ? 'PASS' : 'FAIL'}, source=${item.minApprovalsSource}, selected=${item.selectedRiskLabel || '(none)'}, inferred=${item.inferredRisk || '(none)'}`,
    );
    if (item.errors.length > 0) {
      for (const error of item.errors) {
        lines.push(`  - error: ${error}`);
      }
    }
    if (item.warnings.length > 0) {
      for (const warning of item.warnings) {
        lines.push(`  - warning: ${warning}`);
      }
    }
  }

  return `${lines.join('\n')}\n`;
}

function persistReport(report) {
  ensureDirectory(OUTPUT_JSON_PATH);
  fs.writeFileSync(OUTPUT_JSON_PATH, `${JSON.stringify(report, null, 2)}\n`);
  const markdown = buildMarkdown(report);
  ensureDirectory(OUTPUT_MD_PATH);
  fs.writeFileSync(OUTPUT_MD_PATH, markdown);
  process.stdout.write(markdown);
}

function main() {
  const options = parseArgs(process.argv);
  const prNumber = toPositiveInt(options.prNumber ?? process.env.PR_NUMBER);
  if (!prNumber) {
    throw new Error('PR number is required (--pr or PR_NUMBER).');
  }
  if (!options.repository) {
    throw new Error('Repository is required (--repo or GITHUB_REPOSITORY).');
  }
  if (!process.env.GITHUB_TOKEN && !process.env.GH_TOKEN) {
    throw new Error('GITHUB_TOKEN or GH_TOKEN is required.');
  }

  const scenarios = [
    { scenarioId: 'team-default', reviewTopology: '', approvalOverride: '' },
    { scenarioId: 'solo', reviewTopology: 'solo', approvalOverride: '' },
    { scenarioId: 'team-override-2', reviewTopology: 'team', approvalOverride: '2' },
  ].map((scenario) => runPolicyGateScenario({
    ...scenario,
    prNumber,
    repository: options.repository,
  }));

  const report = {
    generatedAtUtc: new Date().toISOString(),
    repository: options.repository,
    prNumber,
    scenarios,
  };

  persistReport(report);
}

try {
  main();
} catch (error) {
  const message = error instanceof Error ? error.stack || error.message : String(error);
  process.stderr.write(`[review-topology-matrix] ${message}\n`);
  process.exit(1);
}
