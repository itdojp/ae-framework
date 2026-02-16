#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const USEFULNESS_SCHEMA_VERSION = 'usefulness-evaluation/v1';
export const EXIT_POLICY_FAILED = 1;
export const EXIT_INVALID_INPUT = 2;

const DEFAULT_PATHS = {
  runIndex: path.join('artifacts', 'runs', 'index.json'),
  traceability: path.join('traceability.json'),
  verifyProfile: path.join('artifacts', 'verify-profile-summary.json'),
  qualityReport: path.join('reports', 'quality-gates', 'quality-report-ci-latest.json'),
  runManifestCheck: path.join('artifacts', 'run-manifest-check.json'),
  outJson: path.join('artifacts', 'evaluation', 'ae-framework-usefulness-latest.json'),
  outMarkdown: path.join('artifacts', 'evaluation', 'ae-framework-usefulness-latest.md'),
};

const RUN_SUCCESS_VALUES = new Set(['success', 'passed', 'pass', 'ok', 'green', 'completed']);
const RUN_FAILURE_VALUES = new Set(['failure', 'failed', 'error', 'red', 'cancelled', 'timed_out']);
const STEP_PASS_VALUES = new Set(['passed', 'success']);
const STEP_SKIP_VALUES = new Set(['skipped', 'pending']);

function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

function toFiniteNumber(value) {
  const parsed = Number(value);
  return Number.isFinite(parsed) ? parsed : null;
}

function normalizeRatio(value) {
  const numeric = toFiniteNumber(value);
  if (numeric === null) {
    return null;
  }
  if (numeric >= 0 && numeric <= 1) {
    return numeric;
  }
  if (numeric > 1 && numeric <= 100) {
    return numeric / 100;
  }
  return null;
}

function average(values) {
  if (values.length === 0) {
    return null;
  }
  return values.reduce((sum, value) => sum + value, 0) / values.length;
}

function scoreBucket(score) {
  if (score >= 85) {
    return 'excellent';
  }
  if (score >= 70) {
    return 'good';
  }
  if (score >= 50) {
    return 'warning';
  }
  return 'critical';
}

function toRelative(cwd, filePath) {
  const rel = path.relative(cwd, filePath);
  return rel && !rel.startsWith('..') ? rel : filePath;
}

function extractRunList(payload) {
  if (!payload) {
    return [];
  }
  if (Array.isArray(payload)) {
    return payload;
  }
  if (Array.isArray(payload.runs)) {
    return payload.runs;
  }
  if (Array.isArray(payload.items)) {
    return payload.items;
  }
  if (Array.isArray(payload.history)) {
    return payload.history;
  }
  if (Array.isArray(payload.entries)) {
    return payload.entries;
  }
  return [];
}

function extractRunTimestamp(run) {
  if (!run || typeof run !== 'object') {
    return null;
  }
  const candidates = [
    run.timestamp,
    run.finishedAt,
    run.finished_at,
    run.completedAt,
    run.completed_at,
    run.startedAt,
    run.started_at,
    run.createdAt,
    run.created_at,
  ];
  for (const candidate of candidates) {
    if (typeof candidate !== 'string') {
      continue;
    }
    const parsed = Date.parse(candidate);
    if (Number.isFinite(parsed)) {
      return parsed;
    }
  }
  return null;
}

function isRunSuccessful(run) {
  if (!run || typeof run !== 'object') {
    return false;
  }
  if (typeof run.ok === 'boolean') {
    return run.ok;
  }
  if (typeof run.success === 'boolean') {
    return run.success;
  }
  if (typeof run.passed === 'boolean') {
    return run.passed;
  }
  const stringCandidates = [
    run.status,
    run.conclusion,
    run.result,
    run.outcome,
    run.state,
    run?.summary?.status,
  ];
  for (const candidate of stringCandidates) {
    if (typeof candidate !== 'string') {
      continue;
    }
    const normalized = candidate.trim().toLowerCase();
    if (RUN_SUCCESS_VALUES.has(normalized)) {
      return true;
    }
    if (RUN_FAILURE_VALUES.has(normalized)) {
      return false;
    }
  }
  return false;
}

function normalizeStepList(verifyProfile) {
  if (!verifyProfile || typeof verifyProfile !== 'object') {
    return [];
  }
  if (Array.isArray(verifyProfile.steps)) {
    return verifyProfile.steps;
  }
  if (verifyProfile.steps && typeof verifyProfile.steps === 'object') {
    return Object.entries(verifyProfile.steps).map(([name, raw]) => {
      if (raw && typeof raw === 'object') {
        return {
          name,
          ...raw,
        };
      }
      return { name, status: 'unknown' };
    });
  }
  return [];
}

function computeReproducibility(runIndex) {
  const runs = extractRunList(runIndex);
  if (runs.length === 0) {
    return {
      available: false,
      score: null,
      reason: 'run index was not found or did not contain run entries',
      details: {
        totalRuns: 0,
      },
    };
  }
  const successCount = runs.filter((run) => isRunSuccessful(run)).length;
  const failureCount = runs.length - successCount;
  const score = Math.round((successCount / runs.length) * 100);
  return {
    available: true,
    score,
    reason: null,
    details: {
      totalRuns: runs.length,
      successRuns: successCount,
      failedRuns: failureCount,
      successRate: Number((successCount / runs.length).toFixed(3)),
    },
  };
}

function computeTraceability(traceability) {
  if (!traceability || typeof traceability !== 'object') {
    return {
      available: false,
      score: null,
      reason: 'traceability summary JSON was not found',
      details: {},
    };
  }

  const ratios = [];
  const total = toFiniteNumber(traceability.total);
  if (total !== null && total > 0) {
    const testsLinked = toFiniteNumber(traceability.testsLinked);
    const implLinked = toFiniteNumber(traceability.implLinked);
    const formalLinked = toFiniteNumber(traceability.formalLinked);
    if (testsLinked !== null) {
      ratios.push(clamp(testsLinked / total, 0, 1));
    }
    if (implLinked !== null) {
      ratios.push(clamp(implLinked / total, 0, 1));
    }
    if (formalLinked !== null) {
      ratios.push(clamp(formalLinked / total, 0, 1));
    }
  }

  if (ratios.length === 0 && traceability.coverage && typeof traceability.coverage === 'object') {
    const tests = normalizeRatio(traceability.coverage.tests);
    const impl = normalizeRatio(traceability.coverage.impl);
    const formal = normalizeRatio(traceability.coverage.formal);
    if (tests !== null) {
      ratios.push(tests);
    }
    if (impl !== null) {
      ratios.push(impl);
    }
    if (formal !== null) {
      ratios.push(formal);
    }
  }

  const avg = average(ratios);
  if (avg === null) {
    return {
      available: false,
      score: null,
      reason: 'traceability coverage metrics were not found',
      details: {
        total: total ?? null,
      },
    };
  }

  return {
    available: true,
    score: Math.round(avg * 100),
    reason: null,
    details: {
      total: total ?? null,
      dimensions: ratios.length,
      averageCoverage: Number(avg.toFixed(3)),
    },
  };
}

function computeAutomation(verifyProfile) {
  const steps = normalizeStepList(verifyProfile);
  if (steps.length === 0) {
    return {
      available: false,
      score: null,
      reason: 'verify profile summary was not found or does not contain steps',
      details: {},
    };
  }

  const requiredSteps = steps.filter((step) => Boolean(step.required));
  const requiredTotal = requiredSteps.length;
  const requiredPassed = requiredSteps.filter((step) => {
    const status = String(step.status ?? '').toLowerCase();
    return STEP_PASS_VALUES.has(status);
  }).length;
  const executed = steps.filter((step) => {
    const status = String(step.status ?? '').toLowerCase();
    return !STEP_SKIP_VALUES.has(status);
  }).length;
  const requiredPassRate = requiredTotal > 0 ? requiredPassed / requiredTotal : 1;
  const executionRate = steps.length > 0 ? executed / steps.length : 0;
  const score = Math.round((requiredPassRate * 0.7 + executionRate * 0.3) * 100);

  return {
    available: true,
    score,
    reason: null,
    details: {
      totalSteps: steps.length,
      executedSteps: executed,
      requiredSteps: requiredTotal,
      requiredPassed,
      requiredPassRate: Number(requiredPassRate.toFixed(3)),
      executionRate: Number(executionRate.toFixed(3)),
    },
  };
}

function computeQualityDetection(runIndex, qualityReport, runManifestCheck) {
  const componentScores = [];
  const details = {};
  const runs = extractRunList(runIndex);

  if (runs.length > 0) {
    const failures = runs.length - runs.filter((run) => isRunSuccessful(run)).length;
    const historyScore = failures > 0 ? 100 : 70;
    componentScores.push(historyScore);
    details.history = {
      totalRuns: runs.length,
      failedRuns: failures,
      score: historyScore,
    };
  }

  if (qualityReport && typeof qualityReport === 'object') {
    const overallScore = toFiniteNumber(qualityReport.overallScore);
    if (overallScore !== null) {
      const normalized = clamp(Math.round(overallScore), 0, 100);
      componentScores.push(normalized);
      details.qualityGate = {
        overallScore: normalized,
      };
    }
  }

  if (runManifestCheck && typeof runManifestCheck === 'object') {
    if (typeof runManifestCheck.ok === 'boolean') {
      const violationCount = Array.isArray(runManifestCheck.violations)
        ? runManifestCheck.violations.length
        : 0;
      const score = runManifestCheck.ok ? 100 : violationCount > 0 ? 80 : 50;
      componentScores.push(score);
      details.freshness = {
        ok: runManifestCheck.ok,
        violations: violationCount,
        score,
      };
    }
  }

  if (componentScores.length === 0 && runs.length > 0) {
    let latestRun = runs[runs.length - 1];
    for (const run of runs) {
      const runTs = extractRunTimestamp(run);
      const latestTs = extractRunTimestamp(latestRun);
      if (runTs !== null && (latestTs === null || runTs > latestTs)) {
        latestRun = run;
      }
    }
    const latestScore = isRunSuccessful(latestRun) ? 85 : 35;
    componentScores.push(latestScore);
    details.latestRun = {
      score: latestScore,
    };
  }

  const avg = average(componentScores);
  if (avg === null) {
    return {
      available: false,
      score: null,
      reason: 'quality detection signals were not found',
      details,
    };
  }

  return {
    available: true,
    score: Math.round(avg),
    reason: null,
    details: {
      ...details,
      components: componentScores.length,
      averageComponentScore: Number(avg.toFixed(3)),
    },
  };
}

function buildInputStatus({ cwd, key, configuredPath, provided, exists, parseError }) {
  return {
    key,
    path: toRelative(cwd, configuredPath),
    provided,
    exists,
    validJson: exists && !parseError,
    error: parseError || null,
  };
}

function readJsonInput(filePath, { existsSyncImpl = fs.existsSync, readFileSyncImpl = fs.readFileSync } = {}) {
  if (!existsSyncImpl(filePath)) {
    return {
      exists: false,
      parseError: 'file_not_found',
      data: null,
    };
  }
  try {
    const raw = readFileSyncImpl(filePath, 'utf8');
    return {
      exists: true,
      parseError: null,
      data: JSON.parse(raw),
    };
  } catch (error) {
    return {
      exists: true,
      parseError: `invalid_json: ${error instanceof Error ? error.message : String(error)}`,
      data: null,
    };
  }
}

function recommend(report) {
  const recommendations = [];
  for (const [axis, payload] of Object.entries(report.axes)) {
    if (!payload.available) {
      recommendations.push(`Provide ${axis} input artifacts to compute this axis.`);
      continue;
    }
    if (typeof payload.score === 'number' && payload.score < 70) {
      recommendations.push(`Improve ${axis} score (current: ${payload.score}).`);
    }
  }
  if (recommendations.length === 0) {
    recommendations.push('Maintain current verification cadence and continue recording artifacts.');
  }
  return recommendations;
}

export function evaluateUsefulness(payload) {
  const axes = {
    reproducibility: computeReproducibility(payload.runIndex),
    traceability: computeTraceability(payload.traceability),
    automation: computeAutomation(payload.verifyProfile),
    qualityDetection: computeQualityDetection(payload.runIndex, payload.qualityReport, payload.runManifestCheck),
  };

  const availableScores = Object.values(axes)
    .map((axis) => axis.score)
    .filter((score) => typeof score === 'number');

  const overallScore = availableScores.length > 0
    ? Math.round(availableScores.reduce((sum, score) => sum + score, 0) / availableScores.length)
    : 0;

  const missingAxes = Object.entries(axes)
    .filter(([, value]) => !value.available)
    .map(([name]) => name);

  const report = {
    schemaVersion: USEFULNESS_SCHEMA_VERSION,
    generatedAt: new Date().toISOString(),
    inputs: payload.inputStatus,
    axes,
    overall: {
      score: overallScore,
      bucket: scoreBucket(overallScore),
      availableAxes: availableScores.length,
      missingAxes,
    },
  };

  return {
    ...report,
    recommendations: recommend(report),
  };
}

export function renderMarkdown(report) {
  const lines = [
    '# AE Framework Usefulness Evaluation',
    '',
    `- Generated at: ${report.generatedAt}`,
    `- Overall score: ${report.overall.score}/100 (${report.overall.bucket})`,
    `- Available axes: ${report.overall.availableAxes}`,
  ];

  if (report.overall.missingAxes.length > 0) {
    lines.push(`- Missing axes: ${report.overall.missingAxes.join(', ')}`);
  } else {
    lines.push('- Missing axes: none');
  }

  lines.push('', '## Axes');
  for (const [name, axis] of Object.entries(report.axes)) {
    const title = name.replace(/([A-Z])/g, ' $1');
    lines.push(`- ${title}: ${axis.available ? `${axis.score}/100` : 'N/A'}`);
    if (!axis.available && axis.reason) {
      lines.push(`  - Reason: ${axis.reason}`);
    }
  }

  lines.push('', '## Recommendations');
  for (const recommendation of report.recommendations) {
    lines.push(`- ${recommendation}`);
  }

  return `${lines.join('\n')}\n`;
}

export function parseArgs(argv) {
  const options = {
    runIndex: DEFAULT_PATHS.runIndex,
    traceability: DEFAULT_PATHS.traceability,
    verifyProfile: DEFAULT_PATHS.verifyProfile,
    qualityReport: DEFAULT_PATHS.qualityReport,
    runManifestCheck: DEFAULT_PATHS.runManifestCheck,
    outJson: DEFAULT_PATHS.outJson,
    outMarkdown: DEFAULT_PATHS.outMarkdown,
    minScore: null,
    strictInputs: false,
    help: false,
    argErrors: [],
    unknown: [],
    provided: {
      runIndex: false,
      traceability: false,
      verifyProfile: false,
      qualityReport: false,
      runManifestCheck: false,
    },
  };

  for (let i = 2; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = argv[i + 1];
    if (arg === '--') {
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--strict-inputs') {
      options.strictInputs = true;
      continue;
    }
    if (arg.startsWith('--min-score=')) {
      const value = toFiniteNumber(arg.slice('--min-score='.length));
      if (value === null) {
        options.argErrors.push('--min-score must be a number');
      } else {
        options.minScore = clamp(Math.round(value), 0, 100);
      }
      continue;
    }
    if (arg === '--min-score') {
      const value = toFiniteNumber(next);
      if (value === null) {
        options.argErrors.push('--min-score requires a numeric value');
      } else {
        options.minScore = clamp(Math.round(value), 0, 100);
        i += 1;
      }
      continue;
    }

    const pathFlags = [
      ['--run-index', 'runIndex'],
      ['--traceability', 'traceability'],
      ['--verify-profile', 'verifyProfile'],
      ['--quality-report', 'qualityReport'],
      ['--run-manifest-check', 'runManifestCheck'],
      ['--out-json', 'outJson'],
      ['--out-markdown', 'outMarkdown'],
    ];
    let consumed = false;
    for (const [flag, key] of pathFlags) {
      if (arg === flag) {
        if (!next || next.startsWith('-')) {
          options.argErrors.push(`${flag} requires a value`);
        } else {
          options[key] = next;
          if (key in options.provided) {
            options.provided[key] = true;
          }
          i += 1;
        }
        consumed = true;
        break;
      }
      if (arg.startsWith(`${flag}=`)) {
        const value = arg.slice(flag.length + 1);
        if (!value) {
          options.argErrors.push(`${flag} requires a value`);
        } else {
          options[key] = value;
          if (key in options.provided) {
            options.provided[key] = true;
          }
        }
        consumed = true;
        break;
      }
    }
    if (consumed) {
      continue;
    }

    options.unknown.push(arg);
  }

  return options;
}

function printHelp() {
  console.log(`Usage: node scripts/evaluation/evaluate-usefulness.mjs [options]

Options:
  --run-index <file>          Run history JSON (default: ${DEFAULT_PATHS.runIndex})
  --traceability <file>       Traceability JSON (default: ${DEFAULT_PATHS.traceability})
  --verify-profile <file>     verify:profile summary JSON (default: ${DEFAULT_PATHS.verifyProfile})
  --quality-report <file>     quality report JSON (default: ${DEFAULT_PATHS.qualityReport})
  --run-manifest-check <file> run-manifest check JSON (default: ${DEFAULT_PATHS.runManifestCheck})
  --out-json <file>           JSON output path (default: ${DEFAULT_PATHS.outJson})
  --out-markdown <file>       Markdown output path (default: ${DEFAULT_PATHS.outMarkdown})
  --min-score <0-100>         Fail with exit 1 when overall score is below threshold
  --strict-inputs             Treat missing/unparseable axis inputs as invalid input (exit 2)
  -h, --help                  Show this help

Exit codes:
  0: report generated successfully (and threshold satisfied)
  1: policy check failed (e.g. --min-score not met)
  2: invalid input / argument error / strict-inputs violation
`);
}

export function runUsefulness(options, {
  cwd = process.cwd(),
  existsSyncImpl = fs.existsSync,
  readFileSyncImpl = fs.readFileSync,
  mkdirSyncImpl = fs.mkdirSync,
  writeFileSyncImpl = fs.writeFileSync,
  logger = console,
} = {}) {
  if (options.help) {
    printHelp();
    return 0;
  }
  if (options.argErrors.length > 0 || options.unknown.length > 0) {
    for (const error of options.argErrors) {
      logger.error(`[usefulness] ${error}`);
    }
    if (options.unknown.length > 0) {
      logger.error(`[usefulness] unknown arguments: ${options.unknown.join(', ')}`);
    }
    logger.error('[usefulness] use --help for usage details');
    return EXIT_INVALID_INPUT;
  }

  const configuredPaths = {
    runIndex: path.resolve(cwd, options.runIndex),
    traceability: path.resolve(cwd, options.traceability),
    verifyProfile: path.resolve(cwd, options.verifyProfile),
    qualityReport: path.resolve(cwd, options.qualityReport),
    runManifestCheck: path.resolve(cwd, options.runManifestCheck),
  };

  const loaded = {
    runIndex: readJsonInput(configuredPaths.runIndex, { existsSyncImpl, readFileSyncImpl }),
    traceability: readJsonInput(configuredPaths.traceability, { existsSyncImpl, readFileSyncImpl }),
    verifyProfile: readJsonInput(configuredPaths.verifyProfile, { existsSyncImpl, readFileSyncImpl }),
    qualityReport: readJsonInput(configuredPaths.qualityReport, { existsSyncImpl, readFileSyncImpl }),
    runManifestCheck: readJsonInput(configuredPaths.runManifestCheck, { existsSyncImpl, readFileSyncImpl }),
  };

  const inputStatus = Object.keys(configuredPaths).map((key) => {
    return buildInputStatus({
      cwd,
      key,
      configuredPath: configuredPaths[key],
      provided: Boolean(options.provided[key]),
      exists: loaded[key].exists,
      parseError: loaded[key].parseError,
    });
  });

  for (const status of inputStatus) {
    if (status.provided && status.error) {
      logger.error(`[usefulness] invalid input (${status.key}): ${status.path} (${status.error})`);
      return EXIT_INVALID_INPUT;
    }
  }

  const report = evaluateUsefulness({
    runIndex: loaded.runIndex.data,
    traceability: loaded.traceability.data,
    verifyProfile: loaded.verifyProfile.data,
    qualityReport: loaded.qualityReport.data,
    runManifestCheck: loaded.runManifestCheck.data,
    inputStatus,
  });

  if (options.strictInputs && report.overall.missingAxes.length > 0) {
    logger.error(`[usefulness] strict-inputs violation: missing axes ${report.overall.missingAxes.join(', ')}`);
    return EXIT_INVALID_INPUT;
  }

  const jsonPath = path.resolve(cwd, options.outJson);
  const markdownPath = path.resolve(cwd, options.outMarkdown);
  const markdown = renderMarkdown(report);

  try {
    mkdirSyncImpl(path.dirname(jsonPath), { recursive: true });
    mkdirSyncImpl(path.dirname(markdownPath), { recursive: true });
    writeFileSyncImpl(jsonPath, JSON.stringify(report, null, 2));
    writeFileSyncImpl(markdownPath, markdown);
  } catch (error) {
    logger.error(`[usefulness] failed to write report: ${error instanceof Error ? error.message : String(error)}`);
    return EXIT_INVALID_INPUT;
  }

  logger.log(`[usefulness] wrote ${toRelative(cwd, jsonPath)}`);
  logger.log(`[usefulness] wrote ${toRelative(cwd, markdownPath)}`);
  logger.log(`[usefulness] overall=${report.overall.score}/100 bucket=${report.overall.bucket}`);

  if (options.minScore !== null && report.overall.score < options.minScore) {
    logger.error(
      `[usefulness] threshold failed: overall ${report.overall.score} < min-score ${options.minScore}`,
    );
    return EXIT_POLICY_FAILED;
  }

  return 0;
}

export function isCliInvocation(argv) {
  if (!argv[1]) {
    return false;
  }
  try {
    return fileURLToPath(import.meta.url) === path.resolve(argv[1]);
  } catch {
    return false;
  }
}

if (isCliInvocation(process.argv)) {
  process.exit(runUsefulness(parseArgs(process.argv)));
}
