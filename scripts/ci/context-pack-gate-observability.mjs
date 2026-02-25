#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { execGhJson } from './lib/gh-exec.mjs';

const DEFAULT_WORKFLOW_ID = 'context-pack-quality-gate.yml';
const DEFAULT_DAYS = 14;
const DEFAULT_MAX_RUNS = 200;
const DEFAULT_MIN_RUNS = 20;
const DEFAULT_FAIL_RATE_THRESHOLD_PERCENT = 5;
const DEFAULT_REPRODUCTION_THRESHOLD_PERCENT = 80;
const DEFAULT_MTTR_THRESHOLD_MINUTES = 120;
const DEFAULT_OUTPUT_JSON = 'artifacts/context-pack/context-pack-gate-observability.json';
const DEFAULT_OUTPUT_MD = 'artifacts/context-pack/context-pack-gate-observability.md';

function toInt(value, fallback, min = 0) {
  const parsed = Number.parseInt(String(value ?? ''), 10);
  if (!Number.isFinite(parsed) || parsed < min) {
    return fallback;
  }
  return parsed;
}

function toNumber(value, fallback, min = 0) {
  const parsed = Number(String(value ?? ''));
  if (!Number.isFinite(parsed) || parsed < min) {
    return fallback;
  }
  return parsed;
}

function parseArgs(argv) {
  const options = {
    repo: process.env.GITHUB_REPOSITORY || '',
    workflowId: DEFAULT_WORKFLOW_ID,
    days: DEFAULT_DAYS,
    maxRuns: DEFAULT_MAX_RUNS,
    minRuns: DEFAULT_MIN_RUNS,
    failRateThresholdPercent: DEFAULT_FAIL_RATE_THRESHOLD_PERCENT,
    reproductionThresholdPercent: DEFAULT_REPRODUCTION_THRESHOLD_PERCENT,
    mttrThresholdMinutes: DEFAULT_MTTR_THRESHOLD_MINUTES,
    outputJsonPath: DEFAULT_OUTPUT_JSON,
    outputMarkdownPath: DEFAULT_OUTPUT_MD,
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    if (arg === '--') {
      break;
    }

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }

    const readValue = (name) => {
      if (!next || next.startsWith('-')) {
        throw new Error(`missing value for ${name}`);
      }
      index += 1;
      return next;
    };

    if (arg === '--repo') {
      options.repo = readValue('--repo');
      continue;
    }
    if (arg.startsWith('--repo=')) {
      options.repo = arg.slice('--repo='.length);
      continue;
    }

    if (arg === '--workflow-id') {
      options.workflowId = readValue('--workflow-id');
      continue;
    }
    if (arg.startsWith('--workflow-id=')) {
      options.workflowId = arg.slice('--workflow-id='.length);
      continue;
    }

    if (arg === '--days') {
      options.days = toInt(readValue('--days'), options.days, 1);
      continue;
    }
    if (arg.startsWith('--days=')) {
      options.days = toInt(arg.slice('--days='.length), options.days, 1);
      continue;
    }

    if (arg === '--max-runs') {
      options.maxRuns = toInt(readValue('--max-runs'), options.maxRuns, 1);
      continue;
    }
    if (arg.startsWith('--max-runs=')) {
      options.maxRuns = toInt(arg.slice('--max-runs='.length), options.maxRuns, 1);
      continue;
    }

    if (arg === '--min-runs') {
      options.minRuns = toInt(readValue('--min-runs'), options.minRuns, 1);
      continue;
    }
    if (arg.startsWith('--min-runs=')) {
      options.minRuns = toInt(arg.slice('--min-runs='.length), options.minRuns, 1);
      continue;
    }

    if (arg === '--fail-rate-threshold') {
      options.failRateThresholdPercent = toNumber(readValue('--fail-rate-threshold'), options.failRateThresholdPercent, 0);
      continue;
    }
    if (arg.startsWith('--fail-rate-threshold=')) {
      options.failRateThresholdPercent = toNumber(arg.slice('--fail-rate-threshold='.length), options.failRateThresholdPercent, 0);
      continue;
    }

    if (arg === '--reproduction-threshold') {
      options.reproductionThresholdPercent = toNumber(readValue('--reproduction-threshold'), options.reproductionThresholdPercent, 0);
      continue;
    }
    if (arg.startsWith('--reproduction-threshold=')) {
      options.reproductionThresholdPercent = toNumber(arg.slice('--reproduction-threshold='.length), options.reproductionThresholdPercent, 0);
      continue;
    }

    if (arg === '--mttr-threshold-minutes') {
      options.mttrThresholdMinutes = toNumber(readValue('--mttr-threshold-minutes'), options.mttrThresholdMinutes, 0);
      continue;
    }
    if (arg.startsWith('--mttr-threshold-minutes=')) {
      options.mttrThresholdMinutes = toNumber(arg.slice('--mttr-threshold-minutes='.length), options.mttrThresholdMinutes, 0);
      continue;
    }

    if (arg === '--output-json') {
      options.outputJsonPath = readValue('--output-json');
      continue;
    }
    if (arg.startsWith('--output-json=')) {
      options.outputJsonPath = arg.slice('--output-json='.length);
      continue;
    }

    if (arg === '--output-md') {
      options.outputMarkdownPath = readValue('--output-md');
      continue;
    }
    if (arg.startsWith('--output-md=')) {
      options.outputMarkdownPath = arg.slice('--output-md='.length);
      continue;
    }

    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(`Context Pack gate observability report\n\n` +
`Usage:\n` +
`  node scripts/ci/context-pack-gate-observability.mjs [options]\n\n` +
`Options:\n` +
`  --repo <owner/repo>                GitHub repository (default: GITHUB_REPOSITORY)\n` +
`  --workflow-id <file-or-id>         Workflow id/path (default: ${DEFAULT_WORKFLOW_ID})\n` +
`  --days <n>                         Observation window in days (default: ${DEFAULT_DAYS})\n` +
`  --max-runs <n>                     Max completed runs to evaluate (default: ${DEFAULT_MAX_RUNS})\n` +
`  --min-runs <n>                     Minimum sample size for blocking judgement (default: ${DEFAULT_MIN_RUNS})\n` +
`  --fail-rate-threshold <pct>        Failure-rate threshold percent (default: ${DEFAULT_FAIL_RATE_THRESHOLD_PERCENT})\n` +
`  --reproduction-threshold <pct>     Failure reproduction threshold percent (default: ${DEFAULT_REPRODUCTION_THRESHOLD_PERCENT})\n` +
`  --mttr-threshold-minutes <n>       Mean MTTR threshold in minutes (default: ${DEFAULT_MTTR_THRESHOLD_MINUTES})\n` +
`  --output-json <path>               Output JSON path (default: ${DEFAULT_OUTPUT_JSON})\n` +
`  --output-md <path>                 Output Markdown path (default: ${DEFAULT_OUTPUT_MD})\n` +
`  --help, -h                         Show this help\n`);
}

function round2(value) {
  if (!Number.isFinite(value)) {
    return null;
  }
  return Math.round(value * 100) / 100;
}

function percentile(values, ratio) {
  if (!Array.isArray(values) || values.length === 0) {
    return null;
  }
  const sorted = [...values].sort((a, b) => a - b);
  const index = Math.max(0, Math.min(sorted.length - 1, Math.ceil(sorted.length * ratio) - 1));
  return sorted[index];
}

function isFailureConclusion(conclusion) {
  const value = String(conclusion || '').toLowerCase();
  return value !== 'success' && value !== 'skipped' && value !== 'neutral' && value !== 'cancelled';
}

function asMs(value) {
  const parsed = Date.parse(String(value || ''));
  return Number.isFinite(parsed) ? parsed : null;
}

function calcDurationMinutes(run) {
  const startMs = asMs(run.run_started_at) ?? asMs(run.created_at);
  const endMs = asMs(run.updated_at) ?? startMs;
  if (!Number.isFinite(startMs) || !Number.isFinite(endMs) || endMs < startMs) {
    return null;
  }
  return (endMs - startMs) / 60_000;
}

function formatPercent(value) {
  return Number.isFinite(value) ? `${value}%` : 'n/a';
}

function buildMarkdown(report) {
  const lines = [
    '# Context Pack Gate Observability',
    '',
    `- Generated at: ${report.generatedAt}`,
    `- Repository: \`${report.repo}\``,
    `- Workflow: \`${report.workflowId}\``,
    `- Observation window: last ${report.window.days} day(s) (cutoff: ${report.window.cutoff})`,
    '',
    '## Run Summary',
    '',
    '| Metric | Value |',
    '| --- | --- |',
    `| Total completed runs | ${report.metrics.totalRuns} |`,
    `| Success runs | ${report.metrics.successRuns} |`,
    `| Failed runs | ${report.metrics.failedRuns} |`,
    `| Failure rate | ${formatPercent(report.metrics.failureRatePercent)} |`,
    `| Mean duration | ${report.metrics.meanDurationMinutes ?? 'n/a'} min |`,
    `| P95 duration | ${report.metrics.p95DurationMinutes ?? 'n/a'} min |`,
    `| Mean MTTR | ${report.metrics.mttr.meanMinutes ?? 'n/a'} min |`,
    `| P95 MTTR | ${report.metrics.mttr.p95Minutes ?? 'n/a'} min |`,
    `| Unresolved failure streaks | ${report.metrics.mttr.unresolvedFailureStreaks} |`,
    `| Failure reproduction rate | ${formatPercent(report.metrics.reproductionRatePercent)} |`,
    '',
    '## Blocking Readiness',
    '',
    `- Decision: **${report.readiness.readyForBlocking ? 'ready' : 'not-ready'}**`,
    `- Fail-rate threshold: <= ${report.thresholds.failRatePercent}%`,
    `- Reproduction threshold: >= ${report.thresholds.reproductionRatePercent}%`,
    `- MTTR threshold: <= ${report.thresholds.mttrMeanMinutes} min`,
    `- Minimum runs: ${report.thresholds.minRuns}`,
    '',
  ];

  if (report.readiness.reasons.length > 0) {
    lines.push('### Reasons');
    lines.push('');
    for (const reason of report.readiness.reasons) {
      lines.push(`- ${reason}`);
    }
  } else {
    lines.push('### Reasons');
    lines.push('');
    lines.push('- All thresholds satisfied.');
  }

  lines.push('');
  lines.push('## Dependency Inventory');
  lines.push('');
  lines.push('| Job | Depends on | Mode |');
  lines.push('| --- | --- | --- |');
  lines.push('| `context-pack-e2e` | `gate` | label/variable controlled (`enforce-context-pack` / `CONTEXT_PACK_ENFORCE_MAIN`) |');
  lines.push('');
  lines.push('## Notes');
  lines.push('');
  lines.push('- This report is generated from GitHub Actions run history via `gh api`.');
  lines.push('- Use with `docs/ci/context-pack-gate-rollout.md` to decide non-blocking -> blocking transition.');

  return `${lines.join('\n')}\n`;
}

function ensureParentDir(filePath) {
  fs.mkdirSync(path.dirname(path.resolve(filePath)), { recursive: true });
}

function fetchWorkflowRuns(repo, workflowId, maxRuns) {
  const collected = [];
  let page = 1;
  while (collected.length < maxRuns) {
    const pageSize = Math.min(100, maxRuns - collected.length);
    const endpoint = `repos/${repo}/actions/workflows/${encodeURIComponent(workflowId)}/runs?per_page=${pageSize}&page=${page}&status=completed`;
    const response = execGhJson(['api', endpoint]);
    const runs = Array.isArray(response.workflow_runs) ? response.workflow_runs : [];
    if (runs.length === 0) {
      break;
    }
    collected.push(...runs);
    if (runs.length < pageSize) {
      break;
    }
    page += 1;
  }
  return collected.slice(0, maxRuns);
}

function summarizeRuns(runs, cutoffMs) {
  const scopedRuns = runs
    .filter((run) => {
      const createdAtMs = asMs(run.created_at);
      return Number.isFinite(createdAtMs) && createdAtMs >= cutoffMs;
    })
    .sort((a, b) => (asMs(a.created_at) ?? 0) - (asMs(b.created_at) ?? 0));

  const totalRuns = scopedRuns.length;
  let successRuns = 0;
  let failedRuns = 0;
  const durations = [];

  const openFailuresByBranch = new Map();
  const mttrDurations = [];

  const runsBySha = new Map();

  for (const run of scopedRuns) {
    const conclusion = String(run.conclusion || '').toLowerCase();
    const isFailure = isFailureConclusion(conclusion);

    if (isFailure) {
      failedRuns += 1;
    } else if (conclusion === 'success') {
      successRuns += 1;
    }

    const durationMinutes = calcDurationMinutes(run);
    if (Number.isFinite(durationMinutes)) {
      durations.push(durationMinutes);
    }

    const branch = String(run.head_branch || 'unknown');
    const createdAtMs = asMs(run.created_at);
    if (isFailure) {
      if (!openFailuresByBranch.has(branch) && Number.isFinite(createdAtMs)) {
        openFailuresByBranch.set(branch, createdAtMs);
      }
    } else if (conclusion === 'success' && openFailuresByBranch.has(branch) && Number.isFinite(createdAtMs)) {
      const failedAtMs = openFailuresByBranch.get(branch);
      if (Number.isFinite(failedAtMs) && createdAtMs >= failedAtMs) {
        mttrDurations.push((createdAtMs - failedAtMs) / 60_000);
      }
      openFailuresByBranch.delete(branch);
    }

    const sha = String(run.head_sha || '');
    if (sha) {
      if (!runsBySha.has(sha)) {
        runsBySha.set(sha, []);
      }
      runsBySha.get(sha).push(run);
    }
  }

  let reproductionCandidates = 0;
  let reproducedFailures = 0;
  for (const groupedRuns of runsBySha.values()) {
    if (groupedRuns.length < 2) {
      continue;
    }
    const sorted = groupedRuns.sort((a, b) => (asMs(a.created_at) ?? 0) - (asMs(b.created_at) ?? 0));
    const first = sorted[0];
    if (!isFailureConclusion(first.conclusion)) {
      continue;
    }
    reproductionCandidates += 1;
    if (sorted.slice(1).some((run) => isFailureConclusion(run.conclusion))) {
      reproducedFailures += 1;
    }
  }

  const failureRatePercent = totalRuns > 0 ? round2((failedRuns / totalRuns) * 100) : null;
  const meanDurationMinutes = durations.length > 0
    ? round2(durations.reduce((sum, value) => sum + value, 0) / durations.length)
    : null;
  const p95DurationMinutes = round2(percentile(durations, 0.95));

  const meanMttrMinutes = mttrDurations.length > 0
    ? round2(mttrDurations.reduce((sum, value) => sum + value, 0) / mttrDurations.length)
    : null;
  const p95MttrMinutes = round2(percentile(mttrDurations, 0.95));

  const reproductionRatePercent = reproductionCandidates > 0
    ? round2((reproducedFailures / reproductionCandidates) * 100)
    : null;

  return {
    totalRuns,
    successRuns,
    failedRuns,
    failureRatePercent,
    meanDurationMinutes,
    p95DurationMinutes,
    mttr: {
      meanMinutes: meanMttrMinutes,
      p95Minutes: p95MttrMinutes,
      recoveries: mttrDurations.length,
      unresolvedFailureStreaks: openFailuresByBranch.size,
    },
    reproductionRatePercent,
    reproductionCandidates,
    reproducedFailures,
  };
}

function evaluateReadiness(metrics, thresholds) {
  const reasons = [];

  if (metrics.totalRuns < thresholds.minRuns) {
    reasons.push(`insufficient sample size: ${metrics.totalRuns} < ${thresholds.minRuns}`);
  }

  if (metrics.failureRatePercent === null || metrics.failureRatePercent > thresholds.failRatePercent) {
    reasons.push(`failure rate threshold not met: ${metrics.failureRatePercent ?? 'n/a'}% > ${thresholds.failRatePercent}%`);
  }

  if (metrics.failedRuns > 0) {
    if (metrics.reproductionRatePercent === null) {
      reasons.push('failure reproduction threshold not met: reproduction rate is n/a (insufficient repeated failure samples)');
    } else if (metrics.reproductionRatePercent < thresholds.reproductionRatePercent) {
      reasons.push(`failure reproduction threshold not met: ${metrics.reproductionRatePercent}% < ${thresholds.reproductionRatePercent}%`);
    }
  }

  const mttrApplicable = metrics.failedRuns > 0;
  if (mttrApplicable && (metrics.mttr.meanMinutes === null || metrics.mttr.meanMinutes > thresholds.mttrMeanMinutes)) {
    reasons.push(`mean MTTR threshold not met: ${metrics.mttr.meanMinutes ?? 'n/a'} min > ${thresholds.mttrMeanMinutes} min`);
  }

  return {
    readyForBlocking: reasons.length === 0,
    reasons,
  };
}

function main() {
  let options;
  try {
    options = parseArgs(process.argv);
  } catch (error) {
    process.stderr.write(`[context-pack-gate-observability] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exit(1);
  }

  if (options.help) {
    printHelp();
    process.exit(0);
  }

  if (!options.repo) {
    process.stderr.write('[context-pack-gate-observability] missing repository. set --repo or GITHUB_REPOSITORY\n');
    process.exit(1);
  }

  const cutoffMs = Date.now() - (options.days * 24 * 60 * 60 * 1000);

  let runs;
  try {
    runs = fetchWorkflowRuns(options.repo, options.workflowId, options.maxRuns);
  } catch (error) {
    process.stderr.write(`[context-pack-gate-observability] failed to fetch workflow runs: ${error instanceof Error ? error.message : String(error)}\n`);
    process.exit(1);
  }

  const metrics = summarizeRuns(runs, cutoffMs);

  const thresholds = {
    minRuns: options.minRuns,
    failRatePercent: options.failRateThresholdPercent,
    reproductionRatePercent: options.reproductionThresholdPercent,
    mttrMeanMinutes: options.mttrThresholdMinutes,
  };

  const readiness = evaluateReadiness(metrics, thresholds);

  const report = {
    schemaVersion: 'context-pack-gate-observability/v1',
    generatedAt: new Date().toISOString(),
    repo: options.repo,
    workflowId: options.workflowId,
    window: {
      days: options.days,
      cutoff: new Date(cutoffMs).toISOString(),
      maxRuns: options.maxRuns,
    },
    metrics,
    thresholds,
    readiness,
  };

  ensureParentDir(options.outputJsonPath);
  ensureParentDir(options.outputMarkdownPath);
  fs.writeFileSync(path.resolve(options.outputJsonPath), `${JSON.stringify(report, null, 2)}\n`, 'utf8');
  fs.writeFileSync(path.resolve(options.outputMarkdownPath), buildMarkdown(report), 'utf8');

  process.stdout.write(`[context-pack-gate-observability] report(json): ${options.outputJsonPath}\n`);
  process.stdout.write(`[context-pack-gate-observability] report(md): ${options.outputMarkdownPath}\n`);
  process.stdout.write(`[context-pack-gate-observability] readiness: ${readiness.readyForBlocking ? 'ready' : 'not-ready'}\n`);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}

export {
  DEFAULT_DAYS,
  DEFAULT_FAIL_RATE_THRESHOLD_PERCENT,
  DEFAULT_MAX_RUNS,
  DEFAULT_MIN_RUNS,
  DEFAULT_MTTR_THRESHOLD_MINUTES,
  DEFAULT_OUTPUT_JSON,
  DEFAULT_OUTPUT_MD,
  DEFAULT_REPRODUCTION_THRESHOLD_PERCENT,
  DEFAULT_WORKFLOW_ID,
  calcDurationMinutes,
  evaluateReadiness,
  fetchWorkflowRuns,
  formatPercent,
  isFailureConclusion,
  main,
  parseArgs,
  percentile,
  round2,
  summarizeRuns,
  toInt,
  toNumber,
};
