#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { buildArtifactMetadata } from '../ci/lib/artifact-metadata.mjs';

const DEFAULT_OUTPUT_JSON = 'artifacts/quality/quality-scorecard.json';
const DEFAULT_OUTPUT_MD = 'artifacts/quality/quality-scorecard.md';
const SCHEMA_VERSION = 'quality-scorecard/v1';
const CONTRACT_ID = 'quality-scorecard.v1';
const DIMENSION_WEIGHTS = {
  artifactIntegrity: 25,
  assuranceCoverage: 25,
  executionHealth: 25,
  policyReadiness: 15,
  performanceRegression: 10,
};

function readRequiredValue(argv, index, option) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`missing value for ${option}`);
  }
  return next;
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    verifyLiteSummary: null,
    reportEnvelope: null,
    assuranceSummary: null,
    harnessHealth: null,
    policyGateSummary: null,
    benchCompare: null,
    formalSummaries: [],
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--verify-lite-summary') {
      options.verifyLiteSummary = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--report-envelope') {
      options.reportEnvelope = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--assurance-summary') {
      options.assuranceSummary = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--harness-health') {
      options.harnessHealth = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--policy-gate-summary') {
      options.policyGateSummary = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--bench-compare') {
      options.benchCompare = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--formal-summary') {
      options.formalSummaries.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  if (options.help) {
    return options;
  }
  if (!options.verifyLiteSummary) {
    throw new Error('--verify-lite-summary is required');
  }
  if (!options.reportEnvelope) {
    throw new Error('--report-envelope is required');
  }
  return options;
}

function printHelp() {
  process.stdout.write(`Usage: node scripts/quality/build-quality-scorecard.mjs --verify-lite-summary <path> --report-envelope <path> [options]

Options:
  --assurance-summary <path>      optional assurance summary
  --harness-health <path>         optional harness health summary
  --policy-gate-summary <path>    optional policy gate summary
  --bench-compare <path>          optional bench compare summary
  --formal-summary <path>         optional formal summary (repeatable; v2 preferred)
  --output-json <path>            output JSON path (default: ${DEFAULT_OUTPUT_JSON})
  --output-md <path>              output Markdown path (default: ${DEFAULT_OUTPUT_MD})
  --help                          show this help
`);
}

function readJson(resolvedPath) {
  return JSON.parse(fs.readFileSync(resolvedPath, 'utf8'));
}

function resolveRequiredArtifact(inputPath, label) {
  const resolvedPath = path.resolve(inputPath);
  if (!fs.existsSync(resolvedPath)) {
    throw new Error(`${label} not found at ${resolvedPath}`);
  }
  return {
    path: inputPath,
    present: true,
    payload: readJson(resolvedPath),
  };
}

function resolveOptionalArtifact(inputPath) {
  if (!inputPath) {
    return {
      path: null,
      present: false,
      payload: null,
    };
  }
  const resolvedPath = path.resolve(inputPath);
  if (!fs.existsSync(resolvedPath)) {
    return {
      path: inputPath,
      present: false,
      payload: null,
    };
  }
  return {
    path: inputPath,
    present: true,
    payload: readJson(resolvedPath),
  };
}

function clampScore(value) {
  return Math.max(0, Math.min(100, Math.round(value)));
}

function pushBlocker(blockers, dimension, code, severity, message, artifactPath) {
  blockers.push({
    dimension,
    code,
    severity,
    message,
    artifactPath: artifactPath ?? null,
  });
}

function createDimension(status, weight, summary, details, score = null) {
  return {
    status,
    score,
    weight,
    summary,
    details,
  };
}

function summarizeArtifactIntegrity(verifyLite, reportEnvelope, blockers) {
  const issues = [];
  const resolvedVerifyLitePath = verifyLite.path ? path.resolve(verifyLite.path) : null;
  if (reportEnvelope.payload?.source !== 'verify-lite') {
    issues.push('Report envelope source is not verify-lite.');
    pushBlocker(
      blockers,
      'artifactIntegrity',
      'report-envelope-source-mismatch',
      'warn',
      'Report envelope source is not verify-lite.',
      reportEnvelope.path,
    );
  }

  const envelopeArtifacts = Array.isArray(reportEnvelope.payload?.artifacts) ? reportEnvelope.payload.artifacts : [];
  const verifyLiteReferenced = envelopeArtifacts.some((entry) => {
    if (typeof entry?.path !== 'string' || entry.path.length === 0) {
      return false;
    }
    if (entry.path === verifyLite.path) {
      return true;
    }
    if (!resolvedVerifyLitePath) {
      return false;
    }
    return path.resolve(entry.path) === resolvedVerifyLitePath;
  });
  if (!verifyLiteReferenced) {
    issues.push('Report envelope does not reference the verify-lite summary.');
    pushBlocker(
      blockers,
      'artifactIntegrity',
      'report-envelope-missing-verify-lite-reference',
      'warn',
      'Report envelope does not reference the verify-lite summary.',
      reportEnvelope.path,
    );
  }

  const status = issues.length > 0 ? 'warn' : 'pass';
  const score = status === 'pass' ? 100 : 70;
  const summary = issues.length > 0
    ? 'Required artifacts are present, but the report envelope linkage needs review.'
    : 'Required artifacts are present and readable.';
  return createDimension(
    status,
    DIMENSION_WEIGHTS.artifactIntegrity,
    summary,
    {
      requiredArtifactCount: 2,
      presentRequiredArtifacts: 2,
      reportEnvelopeSource: reportEnvelope.payload?.source ?? null,
      verifyLiteReferenced,
    },
    score,
  );
}

function summarizeAssuranceCoverage(assurance, blockers) {
  if (!assurance.present || !assurance.payload) {
    return createDimension(
      'missing',
      DIMENSION_WEIGHTS.assuranceCoverage,
      'assurance-summary artifact is not available for this run.',
      {
        missingReason: 'assurance-summary artifact not available',
      },
      null,
    );
  }

  const summary = assurance.payload.summary ?? {};
  const claims = Array.isArray(assurance.payload.claims) ? assurance.payload.claims : [];
  const openCounterexamples = claims.reduce(
    (count, claim) => count + Number(claim?.counterexamples?.open ?? 0),
    0,
  );

  let status = 'pass';
  if ((summary.claimCount ?? 0) < 1 || (summary.unlinkedCounterexamples ?? 0) > 0 || openCounterexamples > 0) {
    status = 'fail';
  } else if (
    (summary.warningClaims ?? 0) > 0
    || (summary.claimsMissingRequiredLanes ?? 0) > 0
    || (summary.claimsMissingRequiredEvidenceKinds ?? 0) > 0
    || (summary.warningCount ?? 0) > 0
  ) {
    status = 'warn';
  }

  if (status === 'fail') {
    if ((summary.claimCount ?? 0) < 1) {
      pushBlocker(
        blockers,
        'assuranceCoverage',
        'assurance-claims-missing',
        'fail',
        'Assurance summary does not contain any claims.',
        assurance.path,
      );
    }
    if ((summary.unlinkedCounterexamples ?? 0) > 0 || openCounterexamples > 0) {
      pushBlocker(
        blockers,
        'assuranceCoverage',
        'assurance-counterexamples-open',
        'fail',
        'Assurance summary reports open or unlinked counterexamples.',
        assurance.path,
      );
    }
  } else if (status === 'warn') {
    pushBlocker(
      blockers,
      'assuranceCoverage',
      'assurance-coverage-warning',
      'warn',
      'Assurance summary reports warning claims or missing lanes/evidence.',
      assurance.path,
    );
  }

  const score = status === 'pass'
    ? 100
    : status === 'warn'
      ? clampScore(
          100
            - (Number(summary.warningClaims ?? 0) * 20)
            - (Number(summary.claimsMissingRequiredLanes ?? 0) * 15)
            - (Number(summary.claimsMissingRequiredEvidenceKinds ?? 0) * 15)
            - (Number(summary.warningCount ?? 0) * 10),
        )
      : 0;

  return createDimension(
    status,
    DIMENSION_WEIGHTS.assuranceCoverage,
    status === 'pass'
      ? 'Assurance summary reports satisfied claims without coverage blockers.'
      : status === 'warn'
        ? 'Assurance summary reports warning claims or incomplete evidence coverage.'
        : 'Assurance summary reports blocking counterexample or claim coverage issues.',
    {
      claimCount: Number(summary.claimCount ?? 0),
      satisfiedClaims: Number(summary.satisfiedClaims ?? 0),
      warningClaims: Number(summary.warningClaims ?? 0),
      warningCount: Number(summary.warningCount ?? 0),
      claimsMissingRequiredLanes: Number(summary.claimsMissingRequiredLanes ?? 0),
      claimsMissingRequiredEvidenceKinds: Number(summary.claimsMissingRequiredEvidenceKinds ?? 0),
      unlinkedCounterexamples: Number(summary.unlinkedCounterexamples ?? 0),
      openCounterexamples,
    },
    score,
  );
}

function countVerifyLiteStatuses(verifyLitePayload) {
  const steps = verifyLitePayload?.steps ?? {};
  let failed = 0;
  let warned = 0;
  for (const value of Object.values(steps)) {
    const status = String(value?.status ?? 'unknown');
    if (status === 'failure') {
      failed += 1;
    } else if (status === 'pending' || status === 'unknown') {
      warned += 1;
    }
  }
  return { failed, warned };
}

function selectFormalSummary(formalSummaries) {
  const candidates = formalSummaries
    .map((entry) => resolveOptionalArtifact(entry))
    .filter((entry) => entry.present && entry.payload);
  const preferred = candidates.find((entry) => entry.payload?.schemaVersion === 'formal-summary/v2');
  return preferred ?? candidates[0] ?? { path: null, present: false, payload: null };
}

function summarizeExecutionHealth(verifyLite, harnessHealth, formalSummary, blockers) {
  const verifyLiteCounts = countVerifyLiteStatuses(verifyLite.payload);
  const harnessSeverity = harnessHealth.payload?.severity ?? null;
  const formalStatus = formalSummary.payload?.status ?? null;
  const failedFormalResults = Array.isArray(formalSummary.payload?.results)
    ? formalSummary.payload.results.filter((entry) => entry?.status === 'failed').length
    : 0;

  let status = 'pass';
  if (verifyLiteCounts.failed > 0 || harnessSeverity === 'critical' || formalStatus === 'failed' || failedFormalResults > 0) {
    status = 'fail';
  } else if (verifyLiteCounts.warned > 0 || harnessSeverity === 'warn' || formalStatus === 'unknown') {
    status = 'warn';
  }

  if (verifyLiteCounts.failed > 0) {
    pushBlocker(
      blockers,
      'executionHealth',
      'verify-lite-step-failure',
      'fail',
      'verify-lite summary reports failed steps.',
      verifyLite.path,
    );
  }
  if (harnessSeverity === 'critical') {
    pushBlocker(
      blockers,
      'executionHealth',
      'harness-health-critical',
      'fail',
      'Harness health severity is critical.',
      harnessHealth.path,
    );
  } else if (harnessSeverity === 'warn') {
    pushBlocker(
      blockers,
      'executionHealth',
      'harness-health-warn',
      'warn',
      'Harness health reports warnings.',
      harnessHealth.path,
    );
  }
  if (formalStatus === 'failed' || failedFormalResults > 0) {
    pushBlocker(
      blockers,
      'executionHealth',
      'formal-summary-failed',
      'fail',
      'Formal summary reports failed results.',
      formalSummary.path,
    );
  }

  const score = status === 'pass'
    ? 100
    : status === 'warn'
      ? 70
      : 0;
  return createDimension(
    status,
    DIMENSION_WEIGHTS.executionHealth,
    status === 'pass'
      ? 'verify-lite and available health summaries are green.'
      : status === 'warn'
        ? 'Execution health contains non-blocking warnings.'
        : 'Execution health contains blocking failures.',
    {
      verifyLiteFailedSteps: verifyLiteCounts.failed,
      verifyLiteWarnSteps: verifyLiteCounts.warned,
      harnessSeverity,
      formalStatus,
      failedFormalResults,
    },
    score,
  );
}

function summarizePolicyReadiness(policyGate, blockers) {
  if (!policyGate.present || !policyGate.payload) {
    return createDimension(
      'missing',
      DIMENSION_WEIGHTS.policyReadiness,
      'policy-gate summary is not available for this run.',
      {
        missingReason: 'policy-gate summary not available',
      },
      null,
    );
  }

  const evaluation = policyGate.payload.evaluation ?? {};
  const missingRequiredLabels = Array.isArray(evaluation.missingRequiredLabels)
    ? evaluation.missingRequiredLabels
    : [];
  const errorCount = Array.isArray(evaluation.errors) ? evaluation.errors.length : 0;
  const warningCount = Array.isArray(evaluation.warnings) ? evaluation.warnings.length : 0;
  const ok = evaluation.ok === true;

  let status = 'pass';
  if (!ok || missingRequiredLabels.length > 0 || errorCount > 0) {
    status = 'fail';
  } else if (warningCount > 0) {
    status = 'warn';
  }

  if (status === 'fail') {
    pushBlocker(
      blockers,
      'policyReadiness',
      'policy-gate-not-ready',
      'fail',
      'Policy gate summary reports blocking errors or missing required labels.',
      policyGate.path,
    );
  } else if (status === 'warn') {
    pushBlocker(
      blockers,
      'policyReadiness',
      'policy-gate-warning',
      'warn',
      'Policy gate summary reports non-blocking warnings.',
      policyGate.path,
    );
  }

  return createDimension(
    status,
    DIMENSION_WEIGHTS.policyReadiness,
    status === 'pass'
      ? 'Policy gate summary reports a merge-ready state.'
      : status === 'warn'
        ? 'Policy gate summary reports warnings but no blocking errors.'
        : 'Policy gate summary reports blocking approval, label, or gate issues.',
    {
      ok,
      approvals: Number(evaluation.approvals ?? 0),
      effectiveMinApprovals: Number(evaluation.effectiveMinApprovals ?? 0),
      missingRequiredLabels,
      errorCount,
      warningCount,
    },
    status === 'pass' ? 100 : status === 'warn' ? 70 : 0,
  );
}

function summarizePerformanceRegression(benchCompare, blockers) {
  if (!benchCompare.present || !benchCompare.payload) {
    return createDimension(
      'missing',
      DIMENSION_WEIGHTS.performanceRegression,
      'bench-compare artifact is not available for this run.',
      {
        candidateCount: 0,
        failingCandidates: 0,
        missingReason: 'bench-compare artifact not available',
      },
      null,
    );
  }

  const candidates = Array.isArray(benchCompare.payload.candidates) ? benchCompare.payload.candidates : [];
  const failingCandidates = candidates.filter((candidate) => candidate?.overall === 'fail');
  const status = failingCandidates.length > 0 ? 'fail' : 'pass';
  if (status === 'fail') {
    pushBlocker(
      blockers,
      'performanceRegression',
      'bench-compare-regression',
      'fail',
      `bench-compare reports ${failingCandidates.length} failing candidate(s).`,
      benchCompare.path,
    );
  }

  return createDimension(
    status,
    DIMENSION_WEIGHTS.performanceRegression,
    status === 'pass'
      ? 'bench-compare reports no threshold regressions.'
      : 'bench-compare reports threshold regressions.',
    {
      candidateCount: candidates.length,
      failingCandidates: failingCandidates.length,
      candidateNames: failingCandidates.map((candidate) => candidate?.name ?? 'unknown'),
    },
    status === 'pass' ? 100 : 0,
  );
}

function computeOverall(dimensions, blockers) {
  const availableDimensions = [];
  const missingDimensions = [];
  let weightedSum = 0;
  let totalWeight = 0;
  let hasFail = false;
  let hasWarn = false;

  for (const [name, dimension] of Object.entries(dimensions)) {
    if (dimension.status === 'missing') {
      missingDimensions.push(name);
      continue;
    }
    availableDimensions.push(name);
    weightedSum += Number(dimension.score ?? 0) * dimension.weight;
    totalWeight += dimension.weight;
    if (dimension.status === 'fail') {
      hasFail = true;
    } else if (dimension.status === 'warn') {
      hasWarn = true;
    }
  }

  return {
    overallStatus: hasFail ? 'fail' : hasWarn ? 'warn' : 'pass',
    overallScore: totalWeight > 0 ? clampScore(weightedSum / totalWeight) : 0,
    availableDimensions,
    missingDimensions,
    blockerCount: blockers.length,
  };
}

export function renderQualityScorecardMarkdown(scorecard) {
  const lines = [
    '# Quality Scorecard',
    '',
    `- overallStatus: ${scorecard.summary.overallStatus}`,
    `- overallScore: ${scorecard.summary.overallScore}`,
    `- reportOnly: ${scorecard.reportOnly}`,
    `- availableDimensions: ${scorecard.summary.availableDimensions.join(', ') || 'none'}`,
    `- missingDimensions: ${scorecard.summary.missingDimensions.join(', ') || 'none'}`,
    '',
    '## Dimensions',
  ];

  for (const [name, dimension] of Object.entries(scorecard.dimensions)) {
    const scoreText = dimension.score === null ? 'n/a' : String(dimension.score);
    lines.push(`- ${name}: ${dimension.status} (score=${scoreText}, weight=${dimension.weight})`);
    lines.push(`  - ${dimension.summary}`);
  }

  lines.push('', '## Blockers');
  if (scorecard.blockers.length === 0) {
    lines.push('- none');
  } else {
    for (const blocker of scorecard.blockers) {
      lines.push(`- [${blocker.severity}] ${blocker.dimension} / ${blocker.code}: ${blocker.message}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

export function buildQualityScorecard(options) {
  const verifyLite = resolveRequiredArtifact(options.verifyLiteSummary, 'verify-lite summary');
  const reportEnvelope = resolveRequiredArtifact(options.reportEnvelope, 'report envelope');
  const assuranceSummary = resolveOptionalArtifact(options.assuranceSummary);
  const harnessHealth = resolveOptionalArtifact(options.harnessHealth);
  const policyGateSummary = resolveOptionalArtifact(options.policyGateSummary);
  const benchCompare = resolveOptionalArtifact(options.benchCompare);
  const formalSummary = selectFormalSummary(options.formalSummaries);
  const blockers = [];

  const dimensions = {
    artifactIntegrity: summarizeArtifactIntegrity(verifyLite, reportEnvelope, blockers),
    assuranceCoverage: summarizeAssuranceCoverage(assuranceSummary, blockers),
    executionHealth: summarizeExecutionHealth(verifyLite, harnessHealth, formalSummary, blockers),
    policyReadiness: summarizePolicyReadiness(policyGateSummary, blockers),
    performanceRegression: summarizePerformanceRegression(benchCompare, blockers),
  };

  return {
    schemaVersion: SCHEMA_VERSION,
    contractId: CONTRACT_ID,
    generatedAt: new Date().toISOString(),
    metadata: buildArtifactMetadata(),
    reportOnly: true,
    inputs: {
      verifyLiteSummary: {
        path: verifyLite.path,
        present: true,
        required: true,
      },
      reportEnvelope: {
        path: reportEnvelope.path,
        present: true,
        required: true,
      },
      assuranceSummary: {
        path: assuranceSummary.path,
        present: assuranceSummary.present,
        required: false,
      },
      harnessHealth: {
        path: harnessHealth.path,
        present: harnessHealth.present,
        required: false,
      },
      policyGateSummary: {
        path: policyGateSummary.path,
        present: policyGateSummary.present,
        required: false,
      },
      benchCompare: {
        path: benchCompare.path,
        present: benchCompare.present,
        required: false,
      },
      formalSummary: formalSummary.present
        ? {
            path: formalSummary.path,
            present: true,
            required: false,
            schemaVersion: formalSummary.payload?.schemaVersion ?? 'formal-summary/v1',
          }
        : null,
    },
    summary: computeOverall(dimensions, blockers),
    dimensions,
    blockers,
  };
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }
  const payload = buildQualityScorecard(options);
  const markdown = renderQualityScorecardMarkdown(payload);
  const outputJsonPath = path.resolve(options.outputJson);
  const outputMdPath = path.resolve(options.outputMd);
  fs.mkdirSync(path.dirname(outputJsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(outputMdPath), { recursive: true });
  fs.writeFileSync(outputJsonPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
  fs.writeFileSync(outputMdPath, markdown, 'utf8');
  process.stdout.write(`[quality-scorecard] wrote ${outputJsonPath}\n`);
  process.stdout.write(`[quality-scorecard] wrote ${outputMdPath}\n`);
  return 0;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  try {
    process.exitCode = run();
  } catch (error) {
    process.stderr.write(`[quality-scorecard] ${error.message}\n`);
    process.exitCode = 1;
  }
}
