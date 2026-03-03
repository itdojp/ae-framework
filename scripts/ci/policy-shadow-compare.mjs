#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';

const DEFAULT_INPUT_PATH = 'artifacts/ci/policy-input-v1.json';
const DEFAULT_JS_DECISION_PATH = 'artifacts/ci/policy-decision-js-v1.json';
const DEFAULT_OPA_DECISION_PATH = 'artifacts/ci/policy-decision-opa-v1.json';
const DEFAULT_COMPARE_REPORT_PATH = 'artifacts/ci/policy-shadow-compare-v1.json';
const DEFAULT_REGO_PATH = 'policy/risk-policy.rego';
const DEFAULT_QUERY = 'data.ae.policy.decision';
const DEFAULT_OPA_BIN = process.env.OPA_BIN || 'opa';

function parseArgs(argv) {
  const options = {
    inputPath: DEFAULT_INPUT_PATH,
    jsDecisionPath: DEFAULT_JS_DECISION_PATH,
    opaDecisionPath: DEFAULT_OPA_DECISION_PATH,
    reportPath: DEFAULT_COMPARE_REPORT_PATH,
    regoPath: DEFAULT_REGO_PATH,
    query: DEFAULT_QUERY,
    opaBin: DEFAULT_OPA_BIN,
    strict: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const value = argv[index];
    if ((value === '--input' || value === '--input-path') && argv[index + 1]) {
      options.inputPath = argv[++index];
      continue;
    }
    if (value.startsWith('--input=')) {
      options.inputPath = value.slice('--input='.length);
      continue;
    }
    if ((value === '--js-decision' || value === '--js-decision-path') && argv[index + 1]) {
      options.jsDecisionPath = argv[++index];
      continue;
    }
    if (value.startsWith('--js-decision=')) {
      options.jsDecisionPath = value.slice('--js-decision='.length);
      continue;
    }
    if ((value === '--opa-decision' || value === '--opa-decision-path') && argv[index + 1]) {
      options.opaDecisionPath = argv[++index];
      continue;
    }
    if (value.startsWith('--opa-decision=')) {
      options.opaDecisionPath = value.slice('--opa-decision='.length);
      continue;
    }
    if ((value === '--report' || value === '--report-path') && argv[index + 1]) {
      options.reportPath = argv[++index];
      continue;
    }
    if (value.startsWith('--report=')) {
      options.reportPath = value.slice('--report='.length);
      continue;
    }
    if ((value === '--policy' || value === '--rego') && argv[index + 1]) {
      options.regoPath = argv[++index];
      continue;
    }
    if (value.startsWith('--policy=')) {
      options.regoPath = value.slice('--policy='.length);
      continue;
    }
    if (value.startsWith('--rego=')) {
      options.regoPath = value.slice('--rego='.length);
      continue;
    }
    if ((value === '--query') && argv[index + 1]) {
      options.query = argv[++index];
      continue;
    }
    if (value.startsWith('--query=')) {
      options.query = value.slice('--query='.length);
      continue;
    }
    if ((value === '--opa-bin') && argv[index + 1]) {
      options.opaBin = argv[++index];
      continue;
    }
    if (value.startsWith('--opa-bin=')) {
      options.opaBin = value.slice('--opa-bin='.length);
      continue;
    }
    if (value === '--strict') {
      options.strict = true;
    }
  }

  return options;
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function writeJson(filePath, value) {
  ensureDirectory(filePath);
  fs.writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`);
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function appendStepSummary(markdown) {
  const summaryPath = process.env.GITHUB_STEP_SUMMARY;
  if (!summaryPath) return;
  ensureDirectory(summaryPath);
  fs.appendFileSync(summaryPath, markdown);
}

function defaultCommandRunner(command, args) {
  return spawnSync(command, args, {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
}

function normalizeString(value) {
  return typeof value === 'string' ? value.trim() : '';
}

function toIntOrNull(value) {
  const number = Number(value);
  if (!Number.isFinite(number)) return null;
  return Math.trunc(number);
}

function uniqueSortedStrings(value) {
  if (!Array.isArray(value)) return [];
  return [...new Set(value.map((item) => normalizeString(item)).filter(Boolean))].sort();
}

function normalizeCheckStatuses(value, keyName) {
  if (!Array.isArray(value)) return [];
  const statuses = [];
  for (const item of value) {
    if (!item || typeof item !== 'object') continue;
    const key = normalizeString(item[keyName]);
    const status = normalizeString(item?.result?.status);
    if (!key || !status) continue;
    statuses.push(`${key}:${status}`);
  }
  return [...new Set(statuses)].sort();
}

function toEvaluationSnapshot(evaluation) {
  if (!evaluation || typeof evaluation !== 'object') return null;
  return {
    ok: Boolean(evaluation.ok),
    errors: uniqueSortedStrings(evaluation.errors),
    warnings: uniqueSortedStrings(evaluation.warnings),
    inferredRiskLevel: normalizeString(evaluation?.inferredRisk?.level) || null,
    selectedRiskLabel: normalizeString(evaluation?.selectedRiskLabel) || null,
    currentRiskLabels: uniqueSortedStrings(evaluation?.currentRiskLabels),
    reviewTopology: normalizeString(evaluation?.reviewTopology) || null,
    approvals: toIntOrNull(evaluation?.approvals),
    minApprovals: toIntOrNull(evaluation?.minApprovals),
    effectiveMinApprovals: toIntOrNull(evaluation?.effectiveMinApprovals),
    minApprovalsSource: normalizeString(evaluation?.minApprovalsSource) || null,
    requiredLabels: uniqueSortedStrings(evaluation?.requiredLabels),
    missingRequiredLabels: uniqueSortedStrings(evaluation?.missingRequiredLabels),
    requiredCheckStatuses: normalizeCheckStatuses(evaluation?.requiredCheckResults, 'checkName'),
    gateCheckStatuses: normalizeCheckStatuses(evaluation?.gateCheckResults, 'label'),
  };
}

function compareEvaluationSnapshots(jsEvaluation, opaEvaluation) {
  const jsSnapshot = toEvaluationSnapshot(jsEvaluation);
  const opaSnapshot = toEvaluationSnapshot(opaEvaluation);

  if (!jsSnapshot || !opaSnapshot) {
    return {
      match: false,
      jsSnapshot,
      opaSnapshot,
      mismatches: [
        {
          field: 'evaluation',
          js: jsSnapshot,
          opa: opaSnapshot,
        },
      ],
    };
  }

  const mismatches = [];
  for (const field of Object.keys(jsSnapshot)) {
    const jsValue = jsSnapshot[field];
    const opaValue = opaSnapshot[field];
    if (JSON.stringify(jsValue) === JSON.stringify(opaValue)) continue;
    mismatches.push({
      field,
      js: jsValue,
      opa: opaValue,
    });
  }

  return {
    match: mismatches.length === 0,
    jsSnapshot,
    opaSnapshot,
    mismatches,
  };
}

function extractOpaVersion(raw) {
  const stdout = normalizeString(raw?.stdout);
  if (!stdout) return '';
  try {
    const parsed = JSON.parse(stdout);
    return normalizeString(parsed?.version) || normalizeString(parsed?.build_commit) || '';
  } catch {
    const firstLine = stdout.split(/\r?\n/, 1)[0];
    const matched = firstLine.match(/([0-9]+\.[0-9]+\.[0-9]+)/);
    return matched ? matched[1] : firstLine;
  }
}

function resolveOpa(commandRunner, opaBin) {
  const rawWithJson = commandRunner(opaBin, ['version', '--format=json']);
  if (rawWithJson?.error?.code === 'ENOENT') {
    return { available: false, version: '', reason: `opa command not found: ${opaBin}` };
  }
  if (rawWithJson?.status === 0) {
    return {
      available: true,
      version: extractOpaVersion(rawWithJson),
      reason: null,
    };
  }

  const rawPlain = commandRunner(opaBin, ['version']);
  if (rawPlain?.error?.code === 'ENOENT') {
    return { available: false, version: '', reason: `opa command not found: ${opaBin}` };
  }
  if (rawPlain?.status === 0) {
    return {
      available: true,
      version: extractOpaVersion(rawPlain),
      reason: null,
    };
  }

  return {
    available: false,
    version: '',
    reason: normalizeString(rawPlain?.stderr) || normalizeString(rawWithJson?.stderr) || 'opa version command failed',
  };
}

function extractEvalValue(raw) {
  if (raw?.status !== 0) {
    const stderr = normalizeString(raw?.stderr);
    const stdout = normalizeString(raw?.stdout);
    const detail = [stderr, stdout].filter(Boolean).join(' | ');
    throw new Error(detail || 'opa eval failed');
  }

  let parsed;
  try {
    parsed = JSON.parse(String(raw?.stdout || '{}'));
  } catch (error) {
    throw new Error(`opa eval returned invalid JSON: ${error instanceof Error ? error.message : String(error)}`);
  }

  const value = parsed?.result?.[0]?.expressions?.[0]?.value;
  if (!value || typeof value !== 'object') {
    throw new Error('opa eval result does not include data value');
  }
  return value;
}

function evaluateWithOpa({ commandRunner, opaBin, regoPath, inputPath, query }) {
  const raw = commandRunner(opaBin, [
    'eval',
    '--format=json',
    '--data',
    regoPath,
    '--input',
    inputPath,
    query,
  ]);
  if (raw?.error?.code === 'ENOENT') {
    const error = new Error(`opa command not found: ${opaBin}`);
    error.code = 'OPA_NOT_FOUND';
    throw error;
  }
  return extractEvalValue(raw);
}

function buildDecisionArtifact({
  now,
  repository,
  prNumber,
  inputPath,
  engine,
  evaluation,
  unsupportedReason,
  notes,
}) {
  const artifact = {
    schemaVersion: '1.0.0',
    contractId: 'policy-decision.v1',
    generatedAtUtc: now,
    repository,
    prNumber,
    inputPath,
    engine,
    evaluation,
  };
  if (typeof unsupportedReason === 'string' && unsupportedReason.trim()) {
    artifact.unsupportedReason = unsupportedReason.trim();
  }
  if (Array.isArray(notes) && notes.length > 0) {
    artifact.notes = notes;
  }
  return artifact;
}

function buildMarkdownSummary(report) {
  const lines = [
    '### Policy Shadow Compare',
    `- status: ${report.status}`,
    `- PR: #${report.prNumber}`,
    `- opa engine: ${report.engine.status}${report.engine.version ? ` (${report.engine.version})` : ''}`,
  ];

  if (report.comparison) {
    lines.push(`- mismatch count: ${report.comparison.mismatches.length}`);
    if (report.comparison.mismatches.length > 0) {
      lines.push('- mismatch fields:');
      for (const mismatch of report.comparison.mismatches.slice(0, 10)) {
        lines.push(`  - ${mismatch.field}`);
      }
    }
  }

  if (Array.isArray(report.notes) && report.notes.length > 0) {
    lines.push('- notes:');
    for (const note of report.notes) {
      lines.push(`  - ${note}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

function isDirectExecution() {
  const entry = process.argv[1];
  if (!entry) return false;
  return import.meta.url === pathToFileURL(path.resolve(entry)).href;
}

async function runPolicyShadowComparison(
  options = parseArgs(process.argv),
  runtime = { commandRunner: defaultCommandRunner },
) {
  const commandRunner = runtime?.commandRunner || defaultCommandRunner;
  const now = new Date().toISOString();

  const input = readJson(options.inputPath);
  const repository = normalizeString(input?.repository);
  const prNumber = toIntOrNull(input?.prNumber) || 0;

  let jsDecision = null;
  const notes = [];
  try {
    jsDecision = readJson(options.jsDecisionPath);
  } catch (error) {
    notes.push(`js decision is unavailable: ${error instanceof Error ? error.message : String(error)}`);
  }

  const opa = resolveOpa(commandRunner, options.opaBin);
  if (!opa.available) {
    const opaDecision = buildDecisionArtifact({
      now,
      repository,
      prNumber,
      inputPath: options.inputPath,
      engine: {
        kind: 'opa',
        status: 'unsupported',
        version: '',
      },
      evaluation: null,
      unsupportedReason: opa.reason || 'opa is unavailable',
      notes,
    });

    const report = {
      schemaVersion: '1.0.0',
      contractId: 'policy-shadow-compare.v1',
      generatedAtUtc: now,
      repository,
      prNumber,
      inputPath: options.inputPath,
      jsDecisionPath: options.jsDecisionPath,
      opaDecisionPath: options.opaDecisionPath,
      status: 'unsupported',
      engine: opaDecision.engine,
      reason: opa.reason || 'opa is unavailable',
      comparison: null,
      notes,
    };

    writeJson(options.opaDecisionPath, opaDecision);
    writeJson(options.reportPath, report);

    const markdown = buildMarkdownSummary(report);
    appendStepSummary(markdown);
    process.stdout.write(`${markdown}\n`);

    return {
      exitCode: 0,
      report,
      opaDecision,
    };
  }

  let opaEvaluation;
  try {
    opaEvaluation = evaluateWithOpa({
      commandRunner,
      opaBin: options.opaBin,
      regoPath: options.regoPath,
      inputPath: options.inputPath,
      query: options.query,
    });
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    const opaDecision = buildDecisionArtifact({
      now,
      repository,
      prNumber,
      inputPath: options.inputPath,
      engine: {
        kind: 'opa',
        status: 'error',
        version: opa.version || '',
      },
      evaluation: null,
      notes: [...notes, message],
    });

    const report = {
      schemaVersion: '1.0.0',
      contractId: 'policy-shadow-compare.v1',
      generatedAtUtc: now,
      repository,
      prNumber,
      inputPath: options.inputPath,
      jsDecisionPath: options.jsDecisionPath,
      opaDecisionPath: options.opaDecisionPath,
      status: 'error',
      engine: opaDecision.engine,
      reason: message,
      comparison: null,
      notes: [...notes, message],
    };

    writeJson(options.opaDecisionPath, opaDecision);
    writeJson(options.reportPath, report);

    const markdown = buildMarkdownSummary(report);
    appendStepSummary(markdown);
    process.stdout.write(`${markdown}\n`);

    return {
      exitCode: 1,
      report,
      opaDecision,
    };
  }

  const opaDecision = buildDecisionArtifact({
    now,
    repository,
    prNumber,
    inputPath: options.inputPath,
    engine: {
      kind: 'opa',
      status: 'supported',
      version: opa.version || '',
    },
    evaluation: opaEvaluation,
    notes,
  });

  const jsEvaluation = jsDecision?.evaluation || null;
  let comparison = null;
  let status = 'js-missing';
  if (jsEvaluation) {
    comparison = compareEvaluationSnapshots(jsEvaluation, opaEvaluation);
    status = comparison.match ? 'match' : 'mismatch';
  } else {
    notes.push('js decision evaluation is missing; comparison skipped');
  }

  const report = {
    schemaVersion: '1.0.0',
    contractId: 'policy-shadow-compare.v1',
    generatedAtUtc: now,
    repository,
    prNumber,
    inputPath: options.inputPath,
    jsDecisionPath: options.jsDecisionPath,
    opaDecisionPath: options.opaDecisionPath,
    status,
    engine: opaDecision.engine,
    comparison,
    notes,
  };

  writeJson(options.opaDecisionPath, opaDecision);
  writeJson(options.reportPath, report);

  const markdown = buildMarkdownSummary(report);
  appendStepSummary(markdown);
  process.stdout.write(`${markdown}\n`);

  const exitCode = options.strict && status === 'mismatch' ? 1 : 0;
  return {
    exitCode,
    report,
    opaDecision,
  };
}

if (isDirectExecution()) {
  try {
    const result = await runPolicyShadowComparison();
    process.exit(result.exitCode);
  } catch (error) {
    const message = error instanceof Error ? error.stack || error.message : String(error);
    process.stderr.write(`[policy-shadow-compare] ${message}\n`);
    process.exit(1);
  }
}

export {
  compareEvaluationSnapshots,
  parseArgs,
  runPolicyShadowComparison,
  toEvaluationSnapshot,
};
