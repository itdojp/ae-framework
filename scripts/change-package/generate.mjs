#!/usr/bin/env node

import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import {
  DEFAULT_POLICY_PATH,
  collectRequiredLabels,
  getRiskLabels,
  inferRiskLevel,
  loadRiskPolicy,
} from '../ci/lib/risk-policy.mjs';
import { normalizeLabelNames } from '../ci/lib/automation-guards.mjs';

const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/change-package/change-package.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/change-package/change-package.md';
const DEFAULT_ARTIFACT_ROOT = '.';
const DEFAULT_MODE = 'detailed';

const EVIDENCE_CATALOG = [
  {
    id: 'verifyLiteSummary',
    path: 'artifacts/verify-lite/verify-lite-run-summary.json',
    description: 'verify-lite run summary',
  },
  {
    id: 'policyGateSummary',
    path: 'artifacts/ci/policy-gate-summary.json',
    description: 'policy-gate summary',
  },
  {
    id: 'harnessHealth',
    path: 'artifacts/ci/harness-health.json',
    description: 'harness health summary',
  },
  {
    id: 'conformanceSummary',
    path: 'artifacts/hermetic-reports/conformance/summary.json',
    description: 'runtime conformance summary',
  },
  {
    id: 'contextPackSuggestions',
    path: 'artifacts/context-pack/context-pack-suggestions.json',
    description: 'context-pack suggestions summary',
  },
];

function parseChangedFilesEnv(value) {
  if (!value) return [];
  const separators = value.includes('\n') ? '\n' : ',';
  return value
    .split(separators)
    .map((entry) => String(entry || '').trim())
    .filter(Boolean);
}

function toUniqueSorted(values) {
  return [...new Set(values)].sort((left, right) => left.localeCompare(right));
}

function parseLabelsCsv(value) {
  if (!value) return [];
  return value
    .split(',')
    .map((entry) => String(entry || '').trim())
    .filter(Boolean);
}

function parseArgs(argv = process.argv) {
  const options = {
    policyPath: DEFAULT_POLICY_PATH,
    outputJsonPath: DEFAULT_OUTPUT_JSON_PATH,
    outputMarkdownPath: DEFAULT_OUTPUT_MD_PATH,
    changedFilesPath: '',
    artifactRoot: DEFAULT_ARTIFACT_ROOT,
    mode: DEFAULT_MODE,
    repository: '',
    prNumber: null,
    baseRef: '',
    headRef: '',
    intentSummary: '',
    labelsCsv: '',
    eventPath: process.env.GITHUB_EVENT_PATH || '',
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    const readValue = (name) => {
      if (!next || next.startsWith('-')) {
        throw new Error(`missing value for ${name}`);
      }
      index += 1;
      return next;
    };

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--policy') {
      options.policyPath = readValue('--policy');
      continue;
    }
    if (arg.startsWith('--policy=')) {
      options.policyPath = arg.slice('--policy='.length);
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
    if (arg === '--changed-files-file') {
      options.changedFilesPath = readValue('--changed-files-file');
      continue;
    }
    if (arg.startsWith('--changed-files-file=')) {
      options.changedFilesPath = arg.slice('--changed-files-file='.length);
      continue;
    }
    if (arg === '--artifact-root') {
      options.artifactRoot = readValue('--artifact-root');
      continue;
    }
    if (arg.startsWith('--artifact-root=')) {
      options.artifactRoot = arg.slice('--artifact-root='.length);
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
    if (arg === '--repo') {
      options.repository = readValue('--repo');
      continue;
    }
    if (arg.startsWith('--repo=')) {
      options.repository = arg.slice('--repo='.length);
      continue;
    }
    if (arg === '--pr') {
      options.prNumber = Number(readValue('--pr'));
      continue;
    }
    if (arg.startsWith('--pr=')) {
      options.prNumber = Number(arg.slice('--pr='.length));
      continue;
    }
    if (arg === '--base-ref') {
      options.baseRef = readValue('--base-ref');
      continue;
    }
    if (arg.startsWith('--base-ref=')) {
      options.baseRef = arg.slice('--base-ref='.length);
      continue;
    }
    if (arg === '--head-ref') {
      options.headRef = readValue('--head-ref');
      continue;
    }
    if (arg.startsWith('--head-ref=')) {
      options.headRef = arg.slice('--head-ref='.length);
      continue;
    }
    if (arg === '--intent-summary') {
      options.intentSummary = readValue('--intent-summary');
      continue;
    }
    if (arg.startsWith('--intent-summary=')) {
      options.intentSummary = arg.slice('--intent-summary='.length);
      continue;
    }
    if (arg === '--labels') {
      options.labelsCsv = readValue('--labels');
      continue;
    }
    if (arg.startsWith('--labels=')) {
      options.labelsCsv = arg.slice('--labels='.length);
      continue;
    }
    if (arg === '--event-path') {
      options.eventPath = readValue('--event-path');
      continue;
    }
    if (arg.startsWith('--event-path=')) {
      options.eventPath = arg.slice('--event-path='.length);
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(
    `Change Package generator\n\n`
    + `Usage:\n`
    + `  node scripts/change-package/generate.mjs [options]\n\n`
    + `Options:\n`
    + `  --policy <path>               risk policy path (default: ${DEFAULT_POLICY_PATH})\n`
    + `  --output-json <path>          output JSON path (default: ${DEFAULT_OUTPUT_JSON_PATH})\n`
    + `  --output-md <path>            output Markdown path (default: ${DEFAULT_OUTPUT_MD_PATH})\n`
    + `  --changed-files-file <path>   newline-separated changed files input\n`
    + `  --artifact-root <path>        root path for evidence existence checks (default: ${DEFAULT_ARTIFACT_ROOT})\n`
    + `  --mode <digest|detailed>      markdown detail level (default: ${DEFAULT_MODE})\n`
    + `  --repo <owner/repo>           repository override\n`
    + `  --pr <number>                 PR number override\n`
    + `  --base-ref <ref>              base branch override\n`
    + `  --head-ref <ref>              head branch override\n`
    + `  --intent-summary <text>       intent summary override\n`
    + `  --labels <csv>                labels override (comma-separated)\n`
    + `  --event-path <path>           GitHub event JSON path override\n`
    + `  --help, -h                    show help\n`,
  );
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function readJsonIfExists(filePath) {
  if (!filePath || !fs.existsSync(filePath)) {
    return null;
  }
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch {
    return null;
  }
}

function toPositiveInt(value) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) return null;
  const truncated = Math.trunc(parsed);
  if (truncated <= 0) return null;
  return truncated;
}

function runGit(args) {
  try {
    return execFileSync('git', args, { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim();
  } catch {
    return '';
  }
}

function readChangedFilesFromFile(filePath) {
  if (!filePath) return [];
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) {
    throw new Error(`changed files file not found: ${resolved}`);
  }
  return fs.readFileSync(resolved, 'utf8')
    .split('\n')
    .map((line) => line.trim())
    .filter(Boolean);
}

function readChangedFilesFromGit(baseRef) {
  const insideGit = runGit(['rev-parse', '--is-inside-work-tree']);
  if (insideGit !== 'true') return [];

  if (baseRef) {
    // Shallow checkout in CI may not have base ref. Fetch once and ignore failures.
    runGit(['fetch', '--no-tags', '--depth=1', 'origin', baseRef]);
    const fromBase = runGit(['diff', '--name-only', '--diff-filter=ACMR', `origin/${baseRef}...HEAD`]);
    if (fromBase) {
      return fromBase.split('\n').map((entry) => entry.trim()).filter(Boolean);
    }
  }

  const fromLastCommit = runGit(['diff', '--name-only', '--diff-filter=ACMR', 'HEAD~1']);
  if (!fromLastCommit) {
    return [];
  }
  return fromLastCommit.split('\n').map((entry) => entry.trim()).filter(Boolean);
}

function resolveChangedFiles(options, eventPayload, baseRef) {
  const fromFile = readChangedFilesFromFile(options.changedFilesPath);
  if (fromFile.length > 0) {
    return toUniqueSorted(fromFile);
  }

  const envChangedFiles = parseChangedFilesEnv(process.env.CHANGE_PACKAGE_CHANGED_FILES || '');
  if (envChangedFiles.length > 0) {
    return toUniqueSorted(envChangedFiles);
  }

  const payloadChangedFiles = parseChangedFilesEnv(eventPayload?.inputs?.changed_files || '');
  if (payloadChangedFiles.length > 0) {
    return toUniqueSorted(payloadChangedFiles);
  }

  return toUniqueSorted(readChangedFilesFromGit(baseRef));
}

function inferAreaFromFile(filePath) {
  const normalized = String(filePath || '').replace(/\\/g, '/');
  if (!normalized) return 'unknown';
  if (normalized === 'README.md' || normalized.startsWith('docs/')) return 'docs';
  if (normalized === 'package.json' || normalized.endsWith('/package.json') || normalized.endsWith('lock.yaml') || normalized.endsWith('lock.json') || normalized.endsWith('.lock')) {
    return 'dependencies';
  }
  if (normalized.startsWith('.github/workflows/') || normalized.startsWith('scripts/ci/')) return 'ci';
  if (normalized.startsWith('policy/')) return 'policy';
  if (normalized.startsWith('schema/')) return 'schema';
  if (normalized.startsWith('spec/')) return 'spec';
  if (normalized.startsWith('src/')) return 'source';
  if (normalized.startsWith('tests/')) return 'tests';
  if (normalized.startsWith('scripts/')) return 'scripts';
  const [segment] = normalized.split('/');
  return segment || 'unknown';
}

function inferScopeAreas(changedFiles) {
  if (!Array.isArray(changedFiles) || changedFiles.length === 0) {
    return ['unknown'];
  }
  return toUniqueSorted(changedFiles.map(inferAreaFromFile));
}

function resolveRepository(options, eventPayload) {
  const explicit = String(options.repository || '').trim();
  if (explicit) return explicit;
  const fromEnv = String(process.env.GITHUB_REPOSITORY || '').trim();
  if (fromEnv) return fromEnv;
  const fromPayload = String(eventPayload?.repository?.full_name || '').trim();
  if (fromPayload) return fromPayload;
  return null;
}

function resolvePrNumber(options, eventPayload) {
  const fromArgs = toPositiveInt(options.prNumber);
  if (fromArgs) return fromArgs;
  const fromEnv = toPositiveInt(process.env.PR_NUMBER);
  if (fromEnv) return fromEnv;
  return toPositiveInt(
    eventPayload?.pull_request?.number
    || eventPayload?.workflow_run?.pull_requests?.[0]?.number
    || eventPayload?.issue?.number
    || eventPayload?.number
    || eventPayload?.inputs?.pr_number,
  );
}

function resolveBaseRef(options, eventPayload) {
  const fromArgs = String(options.baseRef || '').trim();
  if (fromArgs) return fromArgs;
  const fromEnv = String(process.env.GITHUB_BASE_REF || '').trim();
  if (fromEnv) return fromEnv;
  const fromPayload = String(eventPayload?.pull_request?.base?.ref || '').trim();
  if (fromPayload) return fromPayload;
  return 'main';
}

function resolveHeadRef(options, eventPayload) {
  const fromArgs = String(options.headRef || '').trim();
  if (fromArgs) return fromArgs;
  const fromEnv = String(process.env.GITHUB_HEAD_REF || '').trim();
  if (fromEnv) return fromEnv;
  const fromPayload = String(eventPayload?.pull_request?.head?.ref || '').trim();
  if (fromPayload) return fromPayload;
  const fromGit = runGit(['rev-parse', '--abbrev-ref', 'HEAD']);
  if (fromGit) return fromGit;
  return 'unknown';
}

function resolveCurrentLabels(options, eventPayload) {
  const fromArgs = parseLabelsCsv(options.labelsCsv);
  if (fromArgs.length > 0) return normalizeLabelNames(fromArgs);

  const fromEnv = parseLabelsCsv(process.env.CHANGE_PACKAGE_LABELS || '');
  if (fromEnv.length > 0) return normalizeLabelNames(fromEnv);

  const fromPayload = Array.isArray(eventPayload?.pull_request?.labels)
    ? eventPayload.pull_request.labels.map((label) => label?.name).filter(Boolean)
    : [];
  return normalizeLabelNames(fromPayload);
}

function resolveIntentSummary(options, eventPayload, changedFileCount) {
  const explicit = String(options.intentSummary || '').trim();
  if (explicit) return explicit;

  const fromEnv = String(process.env.CHANGE_PACKAGE_INTENT_SUMMARY || '').trim();
  if (fromEnv) return fromEnv;

  const title = String(eventPayload?.pull_request?.title || '').trim();
  if (title) return title;

  const body = String(eventPayload?.pull_request?.body || '')
    .split('\n')
    .map((line) => line.trim())
    .find(Boolean);
  if (body) return body;

  return changedFileCount > 0
    ? `Update ${changedFileCount} file(s) with policy-bound risk/evidence tracking.`
    : 'Generate policy-bound risk/evidence package.';
}

function buildEvidence(artifactRoot) {
  const resolvedRoot = path.resolve(artifactRoot || '.');
  const items = EVIDENCE_CATALOG.map((item) => {
    const absolutePath = path.resolve(resolvedRoot, item.path);
    return {
      id: item.id,
      path: item.path,
      description: item.description,
      present: fs.existsSync(absolutePath),
    };
  });
  const presentCount = items.filter((item) => item.present).length;
  return {
    artifactRoot: path.relative(process.cwd(), resolvedRoot) || '.',
    items,
    presentCount,
    missingCount: items.length - presentCount,
  };
}

function pushUnique(target, value) {
  if (!value) return;
  if (!target.includes(value)) target.push(value);
}

function buildReproducibilityCommands(requiredLabels) {
  const commands = ['pnpm run verify:lite'];

  if (requiredLabels.includes('run-ci-extended')) {
    pushUnique(commands, 'pnpm run test:ci:extended');
  }
  if (requiredLabels.includes('run-security')) {
    pushUnique(commands, 'pnpm run security:integrated:quick');
  }
  if (requiredLabels.includes('enforce-artifacts')) {
    pushUnique(commands, 'pnpm run artifacts:validate -- --strict=true');
  }
  if (requiredLabels.includes('enforce-testing')) {
    pushUnique(commands, 'pnpm run test:ci:lite');
  }
  if (requiredLabels.includes('enforce-context-pack')) {
    pushUnique(commands, 'pnpm run context-pack:e2e-fixture');
  }

  return commands;
}

function buildMonitoringPlan(requiredLabels) {
  const signals = ['policy-gate.status', 'verify-lite.status', 'harness-health.severity'];
  const alerts = [];

  if (requiredLabels.includes('run-security')) {
    pushUnique(signals, 'security.status');
    pushUnique(alerts, 'security-gate-failed');
  }
  if (requiredLabels.includes('run-ci-extended')) {
    pushUnique(signals, 'ci-extended.status');
    pushUnique(alerts, 'ci-extended-failed');
  }
  if (requiredLabels.includes('enforce-artifacts')) {
    pushUnique(signals, 'artifacts-validate.status');
    pushUnique(alerts, 'artifacts-missing');
  }
  if (requiredLabels.includes('enforce-testing')) {
    pushUnique(signals, 'testing-ddd.status');
    pushUnique(alerts, 'testing-gate-failed');
  }
  if (requiredLabels.includes('enforce-context-pack')) {
    pushUnique(signals, 'context-pack-e2e.status');
    pushUnique(alerts, 'context-pack-gate-failed');
  }

  return { signals, alerts };
}

function buildExceptions({
  missingRequiredLabels,
  selectedRiskLabel,
  inferredRiskLabel,
  currentRiskLabels,
  evidence,
}) {
  const exceptions = [];
  if (missingRequiredLabels.length > 0) {
    exceptions.push({
      code: 'missing-required-labels',
      message: `Missing required labels: ${missingRequiredLabels.join(', ')}`,
    });
  }
  if (currentRiskLabels.length === 0) {
    exceptions.push({
      code: 'missing-risk-label',
      message: 'No risk label is present on the pull request.',
    });
  }
  if (currentRiskLabels.length > 1) {
    exceptions.push({
      code: 'multiple-risk-labels',
      message: `Multiple risk labels are present: ${currentRiskLabels.join(', ')}`,
    });
  }
  if (selectedRiskLabel !== inferredRiskLabel) {
    exceptions.push({
      code: 'risk-label-mismatch',
      message: `Selected risk label (${selectedRiskLabel}) differs from inferred (${inferredRiskLabel})`,
    });
  }
  if (evidence.presentCount === 0) {
    exceptions.push({
      code: 'evidence-empty',
      message: 'No evidence artifact is present under artifact root.',
    });
  }
  return exceptions;
}

function renderDetailedMarkdown(changePackage) {
  const risk = changePackage.risk;
  const evidenceRows = changePackage.evidence.items
    .map((item) => `| ${item.id} | \`${item.path}\` | ${item.present ? 'yes' : 'no'} |`)
    .join('\n');
  const forceTriggers = risk.rationale.forceHighRiskTriggers.length > 0
    ? risk.rationale.forceHighRiskTriggers
      .map((item) => `${item.condition} (${item.ruleId})`)
      .join(', ')
    : '(none)';
  const exceptions = changePackage.exceptions.length > 0
    ? changePackage.exceptions.map((item) => `- ${item.code}: ${item.message}`).join('\n')
    : '- (none)';

  return [
    '## Change Package',
    `- schema: \`${changePackage.schemaVersion}\``,
    `- generatedAt: ${changePackage.generatedAt}`,
    `- policy: \`${changePackage.policyPath}\``,
    '',
    '### Intent',
    `- ${changePackage.intent.summary}`,
    '',
    '### Scope',
    `- changed files: ${changePackage.scope.changedFileCount}`,
    `- areas: ${changePackage.scope.areas.join(', ')}`,
    '',
    '### Risk',
    `- selected: ${risk.selected}`,
    `- inferred: ${risk.inferred}`,
    `- isHighRisk: ${risk.isHighRisk}`,
    `- required labels: ${risk.requiredLabels.length > 0 ? risk.requiredLabels.join(', ') : '(none)'}`,
    `- missing required labels: ${risk.missingRequiredLabels.length > 0 ? risk.missingRequiredLabels.join(', ') : '(none)'}`,
    `- high-risk path matches: ${risk.rationale.highRiskPathMatches.length > 0 ? risk.rationale.highRiskPathMatches.join(', ') : '(none)'}`,
    `- force-high triggers: ${forceTriggers}`,
    '',
    '### Evidence',
    `- present/missing: ${changePackage.evidence.presentCount}/${changePackage.evidence.missingCount}`,
    '',
    '| id | path | present |',
    '| --- | --- | --- |',
    evidenceRows,
    '',
    '### Reproducibility',
    ...changePackage.reproducibility.commands.map((command) => `- \`${command}\``),
    '',
    '### Rollout Plan',
    `- strategy: ${changePackage.rolloutPlan.strategy}`,
    ...changePackage.rolloutPlan.notes.map((note) => `- ${note}`),
    '',
    '### Monitoring Plan',
    `- signals: ${changePackage.monitoringPlan.signals.join(', ') || '(none)'}`,
    `- alerts: ${changePackage.monitoringPlan.alerts.join(', ') || '(none)'}`,
    '',
    '### Exceptions',
    exceptions,
    '',
  ].join('\n');
}

function renderDigestMarkdown(changePackage) {
  const risk = changePackage.risk;
  return [
    '### Change Package',
    `- risk=${risk.selected} (inferred=${risk.inferred}) | files=${changePackage.scope.changedFileCount} | areas=${changePackage.scope.areas.join(', ')} | evidence=${changePackage.evidence.presentCount}/${changePackage.evidence.missingCount} present/missing`,
    `- required labels: ${risk.requiredLabels.length > 0 ? risk.requiredLabels.join(', ') : '(none)'} | missing: ${risk.missingRequiredLabels.length > 0 ? risk.missingRequiredLabels.join(', ') : '(none)'}`,
    `- reproducibility: ${changePackage.reproducibility.commands.map((command) => `\`${command}\``).join(', ')}`,
    '',
  ].join('\n');
}

function renderMarkdown(changePackage, mode) {
  if (mode === 'digest') {
    return renderDigestMarkdown(changePackage);
  }
  return renderDetailedMarkdown(changePackage);
}

function isModeDigest(mode) {
  return String(mode || '').trim().toLowerCase() === 'digest';
}

function buildChangePackage(options, eventPayload) {
  const policy = loadRiskPolicy(options.policyPath);
  const repository = resolveRepository(options, eventPayload);
  const prNumber = resolvePrNumber(options, eventPayload);
  const baseRef = resolveBaseRef(options, eventPayload);
  const headRef = resolveHeadRef(options, eventPayload);
  const changedFiles = resolveChangedFiles(options, eventPayload, baseRef);
  const currentLabels = resolveCurrentLabels(options, eventPayload);
  const currentLabelSet = new Set(currentLabels);

  const riskLabels = getRiskLabels(policy);
  const currentRiskLabels = currentLabels.filter(
    (label) => label === riskLabels.low || label === riskLabels.high,
  );
  const inferredRisk = inferRiskLevel(policy, changedFiles);
  const { requiredLabels } = collectRequiredLabels(policy, changedFiles);

  const selectedRiskLabel = currentRiskLabels.length === 1
    ? currentRiskLabels[0]
    : inferredRisk.level;
  const missingRequiredLabels = requiredLabels.filter((label) => !currentLabelSet.has(label));
  const evidence = buildEvidence(options.artifactRoot);
  const intentSummary = resolveIntentSummary(options, eventPayload, changedFiles.length);
  const monitoringPlan = buildMonitoringPlan(requiredLabels);
  if (missingRequiredLabels.length > 0) {
    pushUnique(monitoringPlan.alerts, 'missing-required-labels');
  }

  const isHighRisk = selectedRiskLabel === riskLabels.high || inferredRisk.level === riskLabels.high;
  const rolloutPlan = {
    strategy: isHighRisk ? 'manual-approval-and-gate-green' : 'auto-merge-when-gates-pass',
    references: [options.policyPath],
    notes: isHighRisk
      ? [
        'High-risk changes require human approval and required gate labels.',
        'Do not merge until required labels/checks are green.',
      ]
      : [
        'Low-risk changes can be merged when required checks are green.',
      ],
  };

  const changePackage = {
    schemaVersion: 'change-package/v1',
    generatedAt: new Date().toISOString(),
    policyPath: options.policyPath,
    source: {
      repository,
      prNumber,
      baseRef,
      headRef,
    },
    intent: {
      summary: intentSummary,
    },
    scope: {
      changedFiles,
      changedFileCount: changedFiles.length,
      areas: inferScopeAreas(changedFiles),
    },
    risk: {
      selected: selectedRiskLabel,
      inferred: inferredRisk.level,
      isHighRisk,
      requiredLabels,
      missingRequiredLabels,
      rationale: {
        highRiskPathMatches: inferredRisk.highRiskPathMatches,
        forceHighRiskTriggers: inferredRisk.forceHighRiskTriggers,
      },
    },
    evidence,
    reproducibility: {
      commands: buildReproducibilityCommands(requiredLabels),
    },
    rolloutPlan,
    monitoringPlan,
    exceptions: buildExceptions({
      missingRequiredLabels,
      selectedRiskLabel,
      inferredRiskLabel: inferredRisk.level,
      currentRiskLabels,
      evidence,
    }),
  };

  return changePackage;
}

function writeOutputs(options, changePackage) {
  const markdown = renderMarkdown(changePackage, isModeDigest(options.mode) ? 'digest' : 'detailed');

  ensureDirectory(options.outputJsonPath);
  fs.writeFileSync(options.outputJsonPath, `${JSON.stringify(changePackage, null, 2)}\n`);

  ensureDirectory(options.outputMarkdownPath);
  fs.writeFileSync(options.outputMarkdownPath, `${markdown.trimEnd()}\n`);

  return markdown;
}

async function run(options = parseArgs(process.argv)) {
  if (options.help) {
    printHelp();
    return null;
  }

  const eventPayload = readJsonIfExists(options.eventPath) || {};
  const changePackage = buildChangePackage(options, eventPayload);
  const markdown = writeOutputs(options, changePackage);
  process.stdout.write(`${markdown.trimEnd()}\n`);
  return changePackage;
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
    process.stderr.write(`[change-package:generate] ${message}\n`);
    process.exit(1);
  }
}

export {
  buildChangePackage,
  parseArgs,
  renderMarkdown,
  run,
};
