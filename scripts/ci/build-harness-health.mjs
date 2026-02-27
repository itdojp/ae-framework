#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import { execGhJson } from './lib/gh-exec.mjs';

const DEFAULT_OUTPUT_JSON = 'artifacts/ci/harness-health.json';
const DEFAULT_OUTPUT_MD = 'artifacts/ci/harness-health.md';
const DEFAULT_MODE = 'digest';

const FAIL_CONCLUSIONS = new Set([
  'FAILURE',
  'CANCELLED',
  'TIMED_OUT',
  'ACTION_REQUIRED',
  'STALE',
  'STARTUP_FAILURE',
]);
const SUCCESS_CONCLUSIONS = new Set(['SUCCESS']);
const SKIP_CONCLUSIONS = new Set(['SKIPPED', 'NEUTRAL']);

const GATE_DEFINITIONS = [
  {
    id: 'artifactsSchema',
    title: 'Artifacts schema',
    recommendedLabels: ['enforce-artifacts'],
    defaultCommands: ['pnpm run artifacts:validate -- --strict=true'],
    matcher: (check) => (
      /^validate-artifacts\s*\//i.test(check.name)
      || /validate-artifacts-ajv/i.test(check.workflowName)
      || (check.workflowName === 'Spec Validation' && /validate-artifacts/i.test(check.name))
    ),
  },
  {
    id: 'testingHarness',
    title: 'Testing harness',
    recommendedLabels: ['enforce-testing'],
    defaultCommands: ['gh workflow run testing-ddd-scripts.yml --repo <owner/repo>'],
    matcher: (check) => (
      check.name === 'testing-ddd'
      || /testing-ddd-scripts/i.test(check.workflowName)
    ),
  },
  {
    id: 'contextPack',
    title: 'Context Pack',
    recommendedLabels: ['enforce-context-pack'],
    defaultCommands: [
      'pnpm run context-pack:deps -- --strict=true',
      'pnpm run context-pack:e2e-fixture',
    ],
    matcher: (check) => (
      /context-pack-e2e/i.test(check.name)
      || /context pack quality gate/i.test(check.workflowName)
    ),
  },
  {
    id: 'runtimeConformance',
    title: 'Runtime Conformance',
    recommendedLabels: ['run-conformance', 'autopilot:on'],
    defaultCommands: [
      'gh workflow run runtime-conformance-self-heal.yml --repo <owner/repo> -f trace_input=samples/conformance/sample-traces.json -f apply_fixes=false -f dry_run=true',
    ],
    matcher: (check) => (
      check.name === 'self-heal'
      || /runtime conformance self-heal/i.test(check.workflowName)
    ),
  },
  {
    id: 'ciExtended',
    title: 'CI Extended',
    recommendedLabels: ['run-ci-extended'],
    defaultCommands: ['gh workflow run ci-extended.yml --repo <owner/repo>'],
    matcher: (check) => (
      /^CI Extended \(/.test(check.name)
      || /^ci[- ]extended(\.yml)?$/i.test(check.workflowName)
    ),
  },
];

function toIsoNow() {
  return new Date().toISOString();
}

function ensureParentDir(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function readJsonIfExists(filePath) {
  if (!filePath || !fs.existsSync(filePath)) {
    return null;
  }
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    return {
      _parseError: error instanceof Error ? error.message : String(error),
    };
  }
}

function parseNumber(value) {
  const parsed = Number(value);
  return Number.isFinite(parsed) ? parsed : null;
}

function parseArgs(argv) {
  const options = {
    repo: process.env.GITHUB_REPOSITORY || '',
    prNumber: null,
    workflow: process.env.GITHUB_WORKFLOW || '',
    runId: parseNumber(process.env.GITHUB_RUN_ID),
    commitSha: process.env.GITHUB_SHA || '',
    mode: DEFAULT_MODE,
    checksJsonPath: '',
    labelsJsonPath: '',
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

    if (arg === '--pr') {
      options.prNumber = parseNumber(readValue('--pr'));
      continue;
    }
    if (arg.startsWith('--pr=')) {
      options.prNumber = parseNumber(arg.slice('--pr='.length));
      continue;
    }

    if (arg === '--workflow') {
      options.workflow = readValue('--workflow');
      continue;
    }
    if (arg.startsWith('--workflow=')) {
      options.workflow = arg.slice('--workflow='.length);
      continue;
    }

    if (arg === '--run-id') {
      options.runId = parseNumber(readValue('--run-id'));
      continue;
    }
    if (arg.startsWith('--run-id=')) {
      options.runId = parseNumber(arg.slice('--run-id='.length));
      continue;
    }

    if (arg === '--commit-sha') {
      options.commitSha = readValue('--commit-sha');
      continue;
    }
    if (arg.startsWith('--commit-sha=')) {
      options.commitSha = arg.slice('--commit-sha='.length);
      continue;
    }

    if (arg === '--mode') {
      options.mode = readValue('--mode');
      continue;
    }
    if (arg.startsWith('--mode=')) {
      options.mode = arg.slice('--mode='.length);
      continue;
    }

    if (arg === '--checks-json') {
      options.checksJsonPath = readValue('--checks-json');
      continue;
    }
    if (arg.startsWith('--checks-json=')) {
      options.checksJsonPath = arg.slice('--checks-json='.length);
      continue;
    }

    if (arg === '--labels-json') {
      options.labelsJsonPath = readValue('--labels-json');
      continue;
    }
    if (arg.startsWith('--labels-json=')) {
      options.labelsJsonPath = arg.slice('--labels-json='.length);
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

  options.mode = String(options.mode || DEFAULT_MODE).toLowerCase() === 'detailed' ? 'detailed' : 'digest';
  if (options.prNumber !== null && (!Number.isInteger(options.prNumber) || options.prNumber <= 0)) {
    throw new Error('--pr must be a positive integer');
  }
  if (options.runId !== null && (!Number.isInteger(options.runId) || options.runId <= 0)) {
    options.runId = null;
  }
  return options;
}

function printHelp() {
  process.stdout.write(
    'Build harness-health summary from gate checks/artifacts.\n\n'
      + 'Usage:\n'
      + '  node scripts/ci/build-harness-health.mjs [options]\n\n'
      + 'Options:\n'
      + '  --repo <owner/repo>        Repository (default: GITHUB_REPOSITORY)\n'
      + '  --pr <number>              Pull request number (loads statusCheckRollup)\n'
      + '  --workflow <name>          Workflow name (default: GITHUB_WORKFLOW)\n'
      + '  --run-id <id>              Workflow run id (default: GITHUB_RUN_ID)\n'
      + '  --commit-sha <sha>         Commit SHA (default: GITHUB_SHA)\n'
      + '  --mode <digest|detailed>   Markdown detail level (default: digest)\n'
      + '  --checks-json <path>       Optional preloaded checks JSON\n'
      + '  --labels-json <path>       Optional preloaded labels JSON array\n'
      + `  --output-json <path>       Output JSON path (default: ${DEFAULT_OUTPUT_JSON})\n`
      + `  --output-md <path>         Output Markdown path (default: ${DEFAULT_OUTPUT_MD})\n`
      + '  --help, -h                 Show this help\n'
  );
}

function normalizeCheckEntry(entry) {
  if (!entry || typeof entry !== 'object') {
    return null;
  }
  const typename = String(entry.__typename || '');
  if (typename && typename !== 'CheckRun' && typename !== 'StatusContext') {
    return null;
  }
  const name = String(entry.name || '').trim();
  if (!name) {
    return null;
  }
  const status = String(entry.status || '').trim().toUpperCase();
  const conclusion = String(entry.conclusion || '').trim().toUpperCase();
  return {
    name,
    status: status || 'COMPLETED',
    conclusion,
    workflowName: String(entry.workflowName || '').trim(),
    detailsUrl: String(entry.detailsUrl || entry.details_url || '').trim(),
    startedAt: String(entry.startedAt || entry.started_at || '').trim(),
    completedAt: String(entry.completedAt || entry.completed_at || '').trim(),
  };
}

function collapseChecksByName(checkRuns) {
  const deduped = new Map();
  for (const check of checkRuns) {
    const key = `${check.workflowName}::${check.name}`;
    const previous = deduped.get(key);
    if (!previous) {
      deduped.set(key, check);
      continue;
    }
    const previousTs = Date.parse(previous.completedAt || previous.startedAt || '');
    const currentTs = Date.parse(check.completedAt || check.startedAt || '');
    if (!Number.isFinite(previousTs) || (Number.isFinite(currentTs) && currentTs >= previousTs)) {
      deduped.set(key, check);
    }
  }
  return Array.from(deduped.values());
}

function listTraceIds(labels) {
  const values = [];
  for (const label of labels) {
    if (label.startsWith('trace:') && label.length > 'trace:'.length) {
      values.push(label.slice('trace:'.length));
    }
  }
  return Array.from(new Set(values));
}

function parseLabelsPayload(payload) {
  if (!payload) {
    return [];
  }
  if (Array.isArray(payload)) {
    return payload
      .map((entry) => {
        if (typeof entry === 'string') {
          return entry.trim();
        }
        if (entry && typeof entry === 'object' && typeof entry.name === 'string') {
          return entry.name.trim();
        }
        return '';
      })
      .filter(Boolean);
  }
  if (payload && typeof payload === 'object' && Array.isArray(payload.labels)) {
    return parseLabelsPayload(payload.labels);
  }
  return [];
}

function buildLocalArtifactsSnapshot() {
  return {
    schemaValidation: readJsonIfExists('artifacts/schema-validation/summary.json'),
    testingRepro: readJsonIfExists('artifacts/testing/repro-summary.json'),
    contextPackDeps: readJsonIfExists('artifacts/context-pack/deps-summary.json'),
    contextPackSuggestions: readJsonIfExists('artifacts/context-pack/context-pack-suggestions.json'),
    runtimeConformance: readJsonIfExists('artifacts/automation/runtime-conformance-self-heal-report.json'),
    heavyTrendSummary: readJsonIfExists('reports/heavy-test-trends-history/summary.json'),
  };
}

function evaluateGateFromChecks(gateDefinition, checkRuns) {
  const matched = collapseChecksByName(checkRuns.filter((check) => gateDefinition.matcher(check)));
  if (matched.length === 0) {
    return {
      status: 'skip',
      reasons: [`${gateDefinition.title}: no related checks detected.`],
      checks: [],
    };
  }

  const failed = matched.filter((check) => FAIL_CONCLUSIONS.has(check.conclusion));
  if (failed.length > 0) {
    return {
      status: 'fail',
      reasons: [
        `${gateDefinition.title}: failing checks (${failed.map((check) => `${check.name}:${check.conclusion || 'UNKNOWN'}`).join(', ')}).`,
      ],
      checks: matched,
    };
  }

  const pending = matched.filter((check) => check.status !== 'COMPLETED');
  if (pending.length > 0) {
    return {
      status: 'warn',
      reasons: [
        `${gateDefinition.title}: pending checks (${pending.map((check) => check.name).join(', ')}).`,
      ],
      checks: matched,
    };
  }

  const succeeded = matched.filter((check) => SUCCESS_CONCLUSIONS.has(check.conclusion));
  if (succeeded.length > 0) {
    return {
      status: 'ok',
      reasons: [],
      checks: matched,
    };
  }

  if (matched.every((check) => SKIP_CONCLUSIONS.has(check.conclusion))) {
    return {
      status: 'skip',
      reasons: [`${gateDefinition.title}: checks skipped.`],
      checks: matched,
    };
  }

  return {
    status: 'warn',
    reasons: [
      `${gateDefinition.title}: inconclusive check state (${matched.map((check) => `${check.name}:${check.conclusion || 'UNKNOWN'}`).join(', ')}).`,
    ],
    checks: matched,
  };
}

function evaluateGateFromLocalArtifacts(gateDefinition, localArtifacts) {
  if (gateDefinition.id === 'artifactsSchema') {
    const summary = localArtifacts.schemaValidation;
    if (!summary || summary._parseError) {
      return {
        status: 'skip',
        reasons: [],
      };
    }
    const errorCount = Number(summary.totals?.errorCount ?? 0);
    if (errorCount > 0) {
      return {
        status: 'fail',
        reasons: [`Artifacts schema: ${errorCount} validation errors detected.`],
      };
    }
    return {
      status: 'ok',
      reasons: [],
    };
  }

  if (gateDefinition.id === 'testingHarness') {
    const summary = localArtifacts.testingRepro;
    if (!summary || summary._parseError || !Array.isArray(summary.records)) {
      return {
        status: 'skip',
        reasons: [],
      };
    }
    const failing = summary.records.filter((record) => ['fail', 'invalid_json'].includes(record.status));
    if (failing.length > 0) {
      return {
        status: 'fail',
        reasons: [`Testing harness: ${failing.length} failing reproducibility records.`],
      };
    }
    return {
      status: summary.records.length > 0 ? 'ok' : 'skip',
      reasons: [],
    };
  }

  if (gateDefinition.id === 'contextPack') {
    const deps = localArtifacts.contextPackDeps;
    if (!deps || deps._parseError) {
      return {
        status: 'skip',
        reasons: [],
      };
    }
    const status = String(deps.status || '').toLowerCase();
    if (status === 'fail') {
      return {
        status: 'fail',
        reasons: [`Context Pack: dependency violations=${deps.violations?.length ?? 0}.`],
      };
    }
    if (status === 'warn') {
      return {
        status: 'warn',
        reasons: [`Context Pack: dependency warnings=${deps.violations?.length ?? 0}.`],
      };
    }
    return {
      status: 'ok',
      reasons: [],
    };
  }

  if (gateDefinition.id === 'ciExtended') {
    const summary = localArtifacts.heavyTrendSummary;
    if (!summary || summary._parseError) {
      return {
        status: 'skip',
        reasons: [],
      };
    }
    const highestSeverity = String(summary.highestSeverity || '').toLowerCase();
    if (highestSeverity === 'critical') {
      return {
        status: 'fail',
        reasons: ['CI Extended: heavy trend summary reached critical severity.'],
      };
    }
    if (highestSeverity === 'warning') {
      return {
        status: 'warn',
        reasons: ['CI Extended: heavy trend summary reached warning severity.'],
      };
    }
    return {
      status: 'ok',
      reasons: [],
    };
  }

  if (gateDefinition.id === 'runtimeConformance') {
    const summary = localArtifacts.runtimeConformance;
    if (!summary || summary._parseError) {
      return {
        status: 'skip',
        reasons: [],
      };
    }
    const status = String(summary.status || '').toLowerCase();
    if (['error', 'failed', 'failure', 'blocked', 'cancelled', 'canceled'].includes(status)) {
      return {
        status: 'fail',
        reasons: [`Runtime Conformance: self-heal status=${status || 'unknown'}.`],
      };
    }
    if (['warn', 'warning', 'degraded', 'partial'].includes(status)) {
      return {
        status: 'warn',
        reasons: [`Runtime Conformance: self-heal status=${status}.`],
      };
    }
    return {
      status: 'ok',
      reasons: [],
    };
  }

  return {
    status: 'skip',
    reasons: [],
  };
}

function deriveSeverity(gates, { forceWarn = false } = {}) {
  const statuses = Object.values(gates).map((gate) => gate.status);
  if (statuses.includes('fail')) {
    return 'critical';
  }
  if (statuses.includes('warn') || forceWarn) {
    return 'warn';
  }
  return 'ok';
}

function dedupeHints(hints) {
  const seen = new Set();
  const result = [];
  for (const hint of hints) {
    const key = `${hint.gate}|${hint.command || ''}|${hint.trace || ''}|${hint.seed || ''}`;
    if (seen.has(key)) {
      continue;
    }
    seen.add(key);
    result.push(hint);
  }
  return result;
}

function buildReproducibleHints(gateResults, labels, localArtifacts) {
  const hints = [];
  const traceIds = listTraceIds(labels);
  for (const trace of traceIds) {
    hints.push({
      gate: 'testingHarness',
      trace,
      seed: null,
      command: `TRACE_ID=${trace} pnpm run test:replay:focus --silent`,
    });
  }

  const testingRepro = localArtifacts.testingRepro;
  if (testingRepro && !testingRepro._parseError && Array.isArray(testingRepro.records)) {
    for (const record of testingRepro.records.slice(0, 10)) {
      hints.push({
        gate: 'testingHarness',
        trace: record.traceId ?? null,
        seed: record.seed ?? null,
        command: record.reproducibleCommand ?? null,
      });
    }
  }

  for (const gateDefinition of GATE_DEFINITIONS) {
    const gate = gateResults[gateDefinition.id];
    if (!gate || !['fail', 'warn'].includes(gate.status)) {
      continue;
    }
    for (const command of gateDefinition.defaultCommands) {
      hints.push({
        gate: gateDefinition.id,
        trace: null,
        seed: null,
        command,
      });
    }
  }

  return dedupeHints(hints).slice(0, 20);
}

function normalizeRecommendedContextChanges(payload) {
  if (!payload || payload._parseError || !Array.isArray(payload.recommendedContextChanges)) {
    return [];
  }
  const normalized = [];
  for (const entry of payload.recommendedContextChanges) {
    if (!entry || typeof entry !== 'object') {
      continue;
    }
    const file = typeof entry.file === 'string' ? entry.file.trim() : '';
    const changeType = typeof entry.changeType === 'string' ? entry.changeType.trim() : '';
    const rationale = typeof entry.rationale === 'string' ? entry.rationale.trim() : '';
    if (!file || !changeType || !rationale) {
      continue;
    }
    normalized.push({
      file,
      changeType,
      targetId: typeof entry.targetId === 'string' && entry.targetId.trim().length > 0 ? entry.targetId.trim() : null,
      rationale,
      suggestedCommand:
        typeof entry.suggestedCommand === 'string' && entry.suggestedCommand.trim().length > 0
          ? entry.suggestedCommand.trim()
          : null,
    });
  }
  return normalized.slice(0, 20);
}

function buildRecommendedContextChanges(gateResults, localArtifacts) {
  const contextPackGate = gateResults.contextPack;
  if (!contextPackGate || !['fail', 'warn'].includes(contextPackGate.status)) {
    return [];
  }
  return normalizeRecommendedContextChanges(localArtifacts.contextPackSuggestions);
}

function buildHarnessHealthReport({
  repo,
  prNumber,
  workflow,
  runId,
  commitSha,
  checkRuns,
  labels,
  localArtifacts,
  extraReasons = [],
}) {
  const gateResults = {};
  const reasons = [...extraReasons];

  for (const definition of GATE_DEFINITIONS) {
    const fromChecks = evaluateGateFromChecks(definition, checkRuns);
    const fromLocal = fromChecks.status === 'skip'
      ? evaluateGateFromLocalArtifacts(definition, localArtifacts)
      : null;

    const finalStatus = fromLocal ? fromLocal.status : fromChecks.status;
    const finalReasons = fromLocal ? fromLocal.reasons : fromChecks.reasons;
    const checks = fromChecks.checks ?? [];
    gateResults[definition.id] = {
      status: finalStatus,
      checks: checks.map((check) => ({
        name: check.name,
        workflowName: check.workflowName,
        status: check.status,
        conclusion: check.conclusion,
        detailsUrl: check.detailsUrl || null,
      })),
      checkCount: checks.length,
    };
    reasons.push(...finalReasons);
  }

  const severity = deriveSeverity(gateResults, { forceWarn: extraReasons.length > 0 });
  const activeGates = Object.entries(gateResults).filter(([, gate]) => ['fail', 'warn'].includes(gate.status));
  const currentLabels = new Set(labels);
  const recommendedLabels = [];
  for (const [gateId] of activeGates) {
    const definition = GATE_DEFINITIONS.find((candidate) => candidate.id === gateId);
    if (!definition) {
      continue;
    }
    for (const label of definition.recommendedLabels) {
      if (!currentLabels.has(label)) {
        recommendedLabels.push(label);
      }
    }
  }

  const recommendedContextChanges = buildRecommendedContextChanges(gateResults, localArtifacts);
  if (gateResults.contextPack) {
    gateResults.contextPack.recommendedContextChanges = recommendedContextChanges;
  }

  return {
    schemaVersion: 'harness-health/v1',
    generatedAt: toIsoNow(),
    repository: repo || null,
    pullRequest: prNumber ?? null,
    commitSha: commitSha || null,
    workflow: workflow || null,
    runId: runId ?? null,
    gates: gateResults,
    severity,
    reasons: Array.from(new Set(reasons)),
    recommendedLabels: Array.from(new Set(recommendedLabels)),
    recommendedContextChanges,
    reproducibleHints: buildReproducibleHints(gateResults, labels, localArtifacts),
  };
}

function renderMarkdown(report, mode) {
  const lines = [
    '## Harness Health',
    `- severity: **${report.severity}**`,
    `- source: workflow=\`${report.workflow || 'unknown'}\`, runId=\`${report.runId ?? 'n/a'}\`, sha=\`${report.commitSha ?? 'n/a'}\``,
    '',
    '| Gate | Status | Checks |',
    '| --- | --- | ---: |',
  ];

  for (const definition of GATE_DEFINITIONS) {
    const gate = report.gates[definition.id];
    lines.push(`| ${definition.id} | ${gate.status} | ${gate.checkCount} |`);
  }

  if (report.recommendedLabels.length > 0) {
    lines.push('');
    lines.push(`- recommended labels: ${report.recommendedLabels.map((label) => `\`${label}\``).join(', ')}`);
  }
  if (Array.isArray(report.recommendedContextChanges) && report.recommendedContextChanges.length > 0) {
    lines.push(`- recommended context changes: ${report.recommendedContextChanges.length}`);
  }

  if (mode === 'detailed') {
    lines.push('');
    lines.push('### Reasons');
    if (report.reasons.length === 0) {
      lines.push('- none');
    } else {
      for (const reason of report.reasons.slice(0, 20)) {
        lines.push(`- ${reason}`);
      }
    }

    lines.push('');
    lines.push('### Reproducible Hints');
    if (report.reproducibleHints.length === 0) {
      lines.push('- none');
    } else {
      for (const hint of report.reproducibleHints.slice(0, 20)) {
        const parts = [];
        if (hint.seed !== null && hint.seed !== undefined) {
          parts.push(`seed=${hint.seed}`);
        }
        if (hint.trace) {
          parts.push(`trace=${hint.trace}`);
        }
        if (hint.command) {
          parts.push(`command=\`${hint.command}\``);
        }
        lines.push(`- ${hint.gate}: ${parts.join(', ') || 'n/a'}`);
      }
    }

    lines.push('');
    lines.push('### Context Pack Suggested Changes');
    if (!Array.isArray(report.recommendedContextChanges) || report.recommendedContextChanges.length === 0) {
      lines.push('- none');
    } else {
      for (const suggestion of report.recommendedContextChanges.slice(0, 20)) {
        const parts = [
          suggestion.changeType,
          suggestion.file,
        ];
        if (suggestion.targetId) {
          parts.push(`target=${suggestion.targetId}`);
        }
        if (suggestion.suggestedCommand) {
          parts.push(`command=\`${suggestion.suggestedCommand}\``);
        }
        parts.push(`rationale=${suggestion.rationale}`);
        lines.push(`- ${parts.join(', ')}`);
      }
    }
  }

  return `${lines.join('\n')}\n`;
}

function loadPrSnapshot(repo, prNumber) {
  if (!repo || !prNumber) {
    return { checkRuns: [], labels: [], commitSha: null, errorMessage: null };
  }
  try {
    const payload = execGhJson([
      'pr',
      'view',
      String(prNumber),
      '--repo',
      repo,
      '--json',
      'statusCheckRollup,labels,headRefOid',
    ]);
    const checkRuns = Array.isArray(payload.statusCheckRollup)
      ? payload.statusCheckRollup.map(normalizeCheckEntry).filter(Boolean)
      : [];
    const labels = parseLabelsPayload(payload.labels);
    const commitSha = typeof payload.headRefOid === 'string' ? payload.headRefOid : null;
    return { checkRuns, labels, commitSha, errorMessage: null };
  } catch (error) {
    return {
      checkRuns: [],
      labels: [],
      commitSha: null,
      errorMessage: error instanceof Error ? error.message : String(error),
    };
  }
}

function writeOutputs(report, outputJsonPath, outputMarkdownPath, mode) {
  ensureParentDir(outputJsonPath);
  fs.writeFileSync(outputJsonPath, `${JSON.stringify(report, null, 2)}\n`);
  ensureParentDir(outputMarkdownPath);
  fs.writeFileSync(outputMarkdownPath, renderMarkdown(report, mode));
}

function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  if (!importMetaUrl || !argvPath) {
    return false;
  }
  const entryPath = path.resolve(String(argvPath));
  const modulePath = fileURLToPath(importMetaUrl);
  return modulePath === entryPath;
}

export {
  buildHarnessHealthReport,
  evaluateGateFromLocalArtifacts,
  collapseChecksByName,
  evaluateGateFromChecks,
  parseArgs,
  renderMarkdown,
};

function main(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return { exitCode: 0 };
  }

  const localArtifacts = buildLocalArtifactsSnapshot();
  const checksPayload = options.checksJsonPath ? readJsonIfExists(options.checksJsonPath) : null;
  const labelsPayload = options.labelsJsonPath ? readJsonIfExists(options.labelsJsonPath) : null;

  let checkRuns = [];
  let labels = [];
  let commitSha = options.commitSha || '';
  const extraReasons = [];

  if (checksPayload && Array.isArray(checksPayload)) {
    checkRuns = checksPayload.map(normalizeCheckEntry).filter(Boolean);
  } else if (options.repo && options.prNumber) {
    const prSnapshot = loadPrSnapshot(options.repo, options.prNumber);
    checkRuns = prSnapshot.checkRuns;
    labels = prSnapshot.labels;
    if (prSnapshot.errorMessage) {
      extraReasons.push(`PR checks could not be loaded via gh: ${prSnapshot.errorMessage}`);
    }
    if (!commitSha && prSnapshot.commitSha) {
      commitSha = prSnapshot.commitSha;
    }
  }

  if (labels.length === 0 && labelsPayload) {
    labels = parseLabelsPayload(labelsPayload);
  }

  const report = buildHarnessHealthReport({
    repo: options.repo,
    prNumber: options.prNumber,
    workflow: options.workflow,
    runId: options.runId,
    commitSha,
    checkRuns,
    labels,
    localArtifacts,
    extraReasons,
  });

  writeOutputs(report, options.outputJsonPath, options.outputMarkdownPath, options.mode);

  process.stdout.write(
    `[harness-health] severity=${report.severity} `
      + `reasons=${report.reasons.length} `
      + `recommendedLabels=${report.recommendedLabels.length}\n`
  );
  process.stdout.write(`[harness-health] report(json): ${options.outputJsonPath}\n`);
  process.stdout.write(`[harness-health] report(md): ${options.outputMarkdownPath}\n`);
  return { exitCode: 0, report };
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  try {
    const result = main(process.argv);
    process.exit(result.exitCode);
  } catch (error) {
    const message = error instanceof Error ? error.stack ?? error.message : String(error);
    process.stderr.write(`[harness-health] ${message}\n`);
    process.exit(1);
  }
}
