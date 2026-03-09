#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const DEFAULT_VERIFY_LITE_SUMMARY_PATH = 'artifacts/verify-lite/verify-lite-run-summary.json';
const DEFAULT_HARNESS_HEALTH_PATH = 'artifacts/ci/harness-health.json';
const DEFAULT_CHANGE_PACKAGE_PATH = 'artifacts/change-package/change-package.json';
const DEFAULT_CONTEXT_PACK_SUGGESTIONS_PATH = 'artifacts/context-pack/context-pack-suggestions.json';
const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/agents/hook-feedback.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/agents/hook-feedback.md';
const FALLBACK_REPRO_COMMAND = 'pnpm run verify:lite';

function uniqueNonEmpty(values) {
  const seen = new Set();
  const result = [];
  for (const value of values) {
    if (typeof value !== 'string') {
      continue;
    }
    const normalized = value.trim();
    if (!normalized || seen.has(normalized)) {
      continue;
    }
    seen.add(normalized);
    result.push(normalized);
  }
  return result;
}

function ensureParentDir(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function readJsonFile(filePath, label) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`${label} could not be read: ${filePath} (${message})`);
  }
}

function readJsonRequired(filePath, label) {
  if (!fs.existsSync(filePath)) {
    throw new Error(`${label} not found: ${filePath}`);
  }
  return readJsonFile(filePath, label);
}

function readJsonOptional(filePath, label) {
  if (!filePath || !fs.existsSync(filePath)) {
    return null;
  }
  return readJsonFile(filePath, label);
}

function summarizeVerifyLite(summary) {
  const failingSteps = [];
  const pendingSteps = [];
  const steps = summary && typeof summary === 'object' ? summary.steps ?? {} : {};
  for (const [stepName, payload] of Object.entries(steps)) {
    const status = typeof payload?.status === 'string' ? payload.status : 'unknown';
    if (status === 'failure') {
      failingSteps.push(stepName);
    } else if (status === 'pending' || status === 'unknown') {
      pendingSteps.push(stepName);
    }
  }

  const traceability = summary && typeof summary === 'object' ? summary.traceability : null;
  if (traceability && typeof traceability === 'object') {
    const traceabilityStatus = typeof traceability.status === 'string' ? traceability.status : 'unknown';
    const missingCount = Number.isFinite(traceability.missingCount) ? Number(traceability.missingCount) : 0;
    if (traceabilityStatus === 'failure' || missingCount > 0) {
      failingSteps.push('traceability');
    } else if (traceabilityStatus === 'pending' || traceabilityStatus === 'unknown') {
      pendingSteps.push('traceability');
    }
  }

  return {
    failingSteps: uniqueNonEmpty(failingSteps),
    pendingSteps: uniqueNonEmpty(pendingSteps),
  };
}

function deriveStatus({ harnessHealth, verifyLiteSummary, changePackage, contextPackSuggestions }) {
  const verifySummary = summarizeVerifyLite(verifyLiteSummary);
  const severity = typeof harnessHealth?.severity === 'string' ? harnessHealth.severity : 'ok';
  const exceptionCount = Array.isArray(changePackage?.exceptions) ? changePackage.exceptions.length : 0;
  const suggestionCount = Array.isArray(contextPackSuggestions?.recommendedContextChanges)
    ? contextPackSuggestions.recommendedContextChanges.length
    : 0;
  const contextStatus = typeof contextPackSuggestions?.status === 'string' ? contextPackSuggestions.status : 'ok';

  if (severity === 'critical' || verifySummary.failingSteps.length > 0) {
    return 'blocked';
  }
  if (
    severity === 'warn'
    || verifySummary.pendingSteps.length > 0
    || exceptionCount > 0
    || (suggestionCount > 0 && contextStatus !== 'success')
  ) {
    return 'warn';
  }
  return 'ok';
}

function buildBlockingReasons({ verifyLiteSummary, harnessHealth, changePackage, contextPackSuggestions }) {
  const verifySummary = summarizeVerifyLite(verifyLiteSummary);
  const reasons = [];

  if (Array.isArray(harnessHealth?.reasons)) {
    reasons.push(...harnessHealth.reasons);
  }
  if (verifySummary.failingSteps.length > 0) {
    reasons.push(`Verify Lite failing steps: ${verifySummary.failingSteps.join(', ')}`);
  }
  if (verifySummary.pendingSteps.length > 0) {
    reasons.push(`Verify Lite incomplete steps: ${verifySummary.pendingSteps.join(', ')}`);
  }
  if (Array.isArray(changePackage?.exceptions)) {
    for (const exception of changePackage.exceptions) {
      const message = typeof exception?.message === 'string' ? exception.message.trim() : '';
      if (message) {
        reasons.push(`Change Package: ${message}`);
      }
    }
  }
  const suggestions = Array.isArray(contextPackSuggestions?.recommendedContextChanges)
    ? contextPackSuggestions.recommendedContextChanges
    : [];
  if (suggestions.length > 0) {
    reasons.push(`Context Pack suggestions pending: ${suggestions.length} change(s)`);
  }

  return uniqueNonEmpty(reasons).slice(0, 10);
}

function toActionSentence(change) {
  const file = typeof change?.file === 'string' && change.file.trim() ? change.file.trim() : 'context-pack input';
  const targetId = typeof change?.targetId === 'string' && change.targetId.trim() ? ` for \`${change.targetId.trim()}\`` : '';
  const changeType = typeof change?.changeType === 'string' && change.changeType.trim() ? ` (${change.changeType.trim()})` : '';
  const command = typeof change?.suggestedCommand === 'string' && change.suggestedCommand.trim()
    ? ` and rerun \`${change.suggestedCommand.trim()}\``
    : '';
  return `Update \`${file}\`${targetId}${changeType}${command}.`;
}

function buildNextActions({ status, verifyLiteSummary, harnessHealth, changePackage, contextPackSuggestions }) {
  const verifySummary = summarizeVerifyLite(verifyLiteSummary);
  const actions = [];

  if (verifySummary.failingSteps.length > 0) {
    actions.push(`Run \`${FALLBACK_REPRO_COMMAND}\` and fix failing verify-lite steps: ${verifySummary.failingSteps.join(', ')}.`);
  }
  if (verifySummary.pendingSteps.length > 0) {
    actions.push(`Re-run incomplete verify-lite steps and confirm: ${verifySummary.pendingSteps.join(', ')}.`);
  }

  const suggestedChanges = uniqueNonEmpty([
    ...(Array.isArray(harnessHealth?.recommendedContextChanges) ? harnessHealth.recommendedContextChanges.map(toActionSentence) : []),
    ...(Array.isArray(contextPackSuggestions?.recommendedContextChanges)
      ? contextPackSuggestions.recommendedContextChanges.map(toActionSentence)
      : []),
  ]);
  actions.push(...suggestedChanges.slice(0, 4));

  const missingRequiredLabels = Array.isArray(changePackage?.risk?.missingRequiredLabels)
    ? uniqueNonEmpty(changePackage.risk.missingRequiredLabels)
    : [];
  if (missingRequiredLabels.length > 0) {
    actions.push(`Add missing required labels (${missingRequiredLabels.join(', ')}) and rerun the gated workflows.`);
  }

  const recommendedLabels = Array.isArray(harnessHealth?.recommendedLabels)
    ? uniqueNonEmpty(harnessHealth.recommendedLabels)
    : [];
  if (recommendedLabels.length > 0) {
    actions.push(`If opt-in reruns are needed, apply labels: ${recommendedLabels.join(', ')}.`);
  }

  if (actions.length === 0) {
    if (status === 'ok') {
      actions.push('Proceed to the next task and rerun `pnpm run verify:lite` after any source change.');
    } else {
      actions.push('Run `pnpm run verify:lite` and regenerate hook feedback artifacts.');
    }
  }

  return uniqueNonEmpty(actions).slice(0, 10);
}

function buildReproCommands({ changePackage, harnessHealth, contextPackSuggestions }) {
  const commands = uniqueNonEmpty([
    ...(Array.isArray(changePackage?.reproducibility?.commands) ? changePackage.reproducibility.commands : []),
    ...(Array.isArray(harnessHealth?.reproducibleHints)
      ? harnessHealth.reproducibleHints.map((hint) => hint?.command)
      : []),
    ...(Array.isArray(contextPackSuggestions?.recommendedContextChanges)
      ? contextPackSuggestions.recommendedContextChanges.map((change) => change?.suggestedCommand)
      : []),
  ]);

  if (commands.length === 0) {
    commands.push(FALLBACK_REPRO_COMMAND);
  }
  return commands.slice(0, 10);
}

function addEvidenceItem(items, item) {
  if (!item || typeof item.path !== 'string' || !item.path.trim()) {
    return;
  }
  if (items.some((candidate) => candidate.path === item.path)) {
    return;
  }
  items.push(item);
}

function buildEvidence({
  verifyLiteSummaryPath,
  harnessHealthPath,
  changePackagePath,
  contextPackSuggestionsPath,
  verifyLiteSummary,
  changePackage,
  harnessHealth,
  contextPackSuggestions,
}) {
  const items = [];

  if (Array.isArray(changePackage?.evidence?.items)) {
    for (const evidence of changePackage.evidence.items) {
      addEvidenceItem(items, {
        id: typeof evidence?.id === 'string' && evidence.id.trim() ? evidence.id.trim() : 'evidence',
        path: String(evidence?.path ?? '').trim(),
        description: typeof evidence?.description === 'string' && evidence.description.trim()
          ? evidence.description.trim()
          : 'referenced evidence',
        present: Boolean(evidence?.present),
        status: null,
      });
    }
  }

  addEvidenceItem(items, {
    id: 'verifyLiteSummary',
    path: verifyLiteSummaryPath,
    description: 'verify-lite run summary',
    present: true,
    status: summarizeVerifyLite(verifyLiteSummary).failingSteps.length > 0 ? 'failure' : 'available',
  });
  addEvidenceItem(items, {
    id: 'harnessHealth',
    path: harnessHealthPath,
    description: 'harness health summary',
    present: true,
    status: typeof harnessHealth?.severity === 'string' ? harnessHealth.severity : null,
  });
  addEvidenceItem(items, {
    id: 'changePackage',
    path: changePackagePath,
    description: 'change package evidence bundle',
    present: true,
    status: typeof changePackage?.risk?.selected === 'string' ? changePackage.risk.selected : null,
  });
  if (contextPackSuggestionsPath && contextPackSuggestions) {
    addEvidenceItem(items, {
      id: 'contextPackSuggestions',
      path: contextPackSuggestionsPath,
      description: 'context-pack suggestion summary',
      present: true,
      status: typeof contextPackSuggestions?.status === 'string' ? contextPackSuggestions.status : null,
    });
  }

  return items;
}

export function buildHookFeedbackArtifact({
  verifyLiteSummary,
  harnessHealth,
  changePackage,
  contextPackSuggestions,
  source,
  now = new Date().toISOString(),
}) {
  const status = deriveStatus({ verifyLiteSummary, harnessHealth, changePackage, contextPackSuggestions });
  return {
    schemaVersion: 'hook-feedback/v1',
    generatedAt: now,
    status,
    blockingReasons: buildBlockingReasons({ verifyLiteSummary, harnessHealth, changePackage, contextPackSuggestions }),
    nextActions: buildNextActions({ status, verifyLiteSummary, harnessHealth, changePackage, contextPackSuggestions }),
    reproCommands: buildReproCommands({ changePackage, harnessHealth, contextPackSuggestions }),
    evidence: buildEvidence({
      verifyLiteSummaryPath: source.verifyLiteSummaryPath,
      harnessHealthPath: source.harnessHealthPath,
      changePackagePath: source.changePackagePath,
      contextPackSuggestionsPath: source.contextPackSuggestionsPath,
      verifyLiteSummary,
      changePackage,
      harnessHealth,
      contextPackSuggestions,
    }),
    source,
  };
}

export function renderMarkdown(artifact) {
  const lines = [
    '# Hook Feedback',
    `- status: **${artifact.status}**`,
    `- generatedAt: \`${artifact.generatedAt}\``,
    '',
    '## Blocking reasons',
  ];

  if (artifact.blockingReasons.length === 0) {
    lines.push('- none');
  } else {
    for (const reason of artifact.blockingReasons) {
      lines.push(`- ${reason}`);
    }
  }

  lines.push('', '## Next actions');
  for (const [index, action] of artifact.nextActions.entries()) {
    lines.push(`${index + 1}. ${action}`);
  }

  lines.push('', '## Repro commands');
  for (const command of artifact.reproCommands) {
    lines.push(`- \`${command}\``);
  }

  lines.push('', '## Evidence', '| id | present | status | path |', '| --- | --- | --- | --- |');
  for (const evidence of artifact.evidence) {
    lines.push(`| ${evidence.id} | ${evidence.present ? 'yes' : 'no'} | ${evidence.status ?? 'n/a'} | \`${evidence.path}\` |`);
  }

  lines.push('', '## Source artifacts');
  lines.push(`- verify-lite: \`${artifact.source.verifyLiteSummaryPath}\``);
  lines.push(`- harness-health: \`${artifact.source.harnessHealthPath}\``);
  lines.push(`- change-package: \`${artifact.source.changePackagePath}\``);
  lines.push(`- context-pack suggestions: \`${artifact.source.contextPackSuggestionsPath ?? 'n/a'}\``);
  return `${lines.join('\n')}\n`;
}

export function parseArgs(argv = process.argv) {
  const options = {
    verifyLiteSummaryPath: DEFAULT_VERIFY_LITE_SUMMARY_PATH,
    harnessHealthPath: DEFAULT_HARNESS_HEALTH_PATH,
    changePackagePath: DEFAULT_CHANGE_PACKAGE_PATH,
    contextPackSuggestionsPath: DEFAULT_CONTEXT_PACK_SUGGESTIONS_PATH,
    outputJsonPath: DEFAULT_OUTPUT_JSON_PATH,
    outputMarkdownPath: DEFAULT_OUTPUT_MD_PATH,
    help: false,
  };

  const readValue = (argvValue, optionName) => {
    if (!argvValue || argvValue.startsWith('-')) {
      throw new Error(`missing value for ${optionName}`);
    }
    return argvValue;
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--verify-lite-summary') {
      options.verifyLiteSummaryPath = readValue(next, '--verify-lite-summary');
      index += 1;
      continue;
    }
    if (arg.startsWith('--verify-lite-summary=')) {
      options.verifyLiteSummaryPath = arg.slice('--verify-lite-summary='.length);
      continue;
    }
    if (arg === '--harness-health') {
      options.harnessHealthPath = readValue(next, '--harness-health');
      index += 1;
      continue;
    }
    if (arg.startsWith('--harness-health=')) {
      options.harnessHealthPath = arg.slice('--harness-health='.length);
      continue;
    }
    if (arg === '--change-package') {
      options.changePackagePath = readValue(next, '--change-package');
      index += 1;
      continue;
    }
    if (arg.startsWith('--change-package=')) {
      options.changePackagePath = arg.slice('--change-package='.length);
      continue;
    }
    if (arg === '--context-pack-suggestions') {
      options.contextPackSuggestionsPath = readValue(next, '--context-pack-suggestions');
      index += 1;
      continue;
    }
    if (arg.startsWith('--context-pack-suggestions=')) {
      options.contextPackSuggestionsPath = arg.slice('--context-pack-suggestions='.length);
      continue;
    }
    if (arg === '--output-json') {
      options.outputJsonPath = readValue(next, '--output-json');
      index += 1;
      continue;
    }
    if (arg.startsWith('--output-json=')) {
      options.outputJsonPath = arg.slice('--output-json='.length);
      continue;
    }
    if (arg === '--output-md') {
      options.outputMarkdownPath = readValue(next, '--output-md');
      index += 1;
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
  process.stdout.write(
    'Build deterministic hook feedback from existing CI artifacts.\n\n'
      + 'Usage:\n'
      + '  node scripts/agents/build-hook-feedback.mjs [options]\n\n'
      + 'Options:\n'
      + `  --verify-lite-summary <path>       Verify Lite summary path (default: ${DEFAULT_VERIFY_LITE_SUMMARY_PATH})\n`
      + `  --harness-health <path>            Harness health path (default: ${DEFAULT_HARNESS_HEALTH_PATH})\n`
      + `  --change-package <path>            Change Package path (default: ${DEFAULT_CHANGE_PACKAGE_PATH})\n`
      + `  --context-pack-suggestions <path>  Optional Context Pack suggestions path (default: ${DEFAULT_CONTEXT_PACK_SUGGESTIONS_PATH})\n`
      + `  --output-json <path>               Output JSON path (default: ${DEFAULT_OUTPUT_JSON_PATH})\n`
      + `  --output-md <path>                 Output Markdown path (default: ${DEFAULT_OUTPUT_MD_PATH})\n`
      + '  --help, -h                         Show help\n',
  );
}

export function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  if (!argvPath) {
    return false;
  }
  return fileURLToPath(importMetaUrl) === path.resolve(argvPath);
}

export function run(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return { exitCode: 0 };
  }

  const verifyLiteSummaryPath = path.resolve(options.verifyLiteSummaryPath);
  const harnessHealthPath = path.resolve(options.harnessHealthPath);
  const changePackagePath = path.resolve(options.changePackagePath);
  const contextPackSuggestionsPath = options.contextPackSuggestionsPath
    ? path.resolve(options.contextPackSuggestionsPath)
    : null;
  const outputJsonPath = path.resolve(options.outputJsonPath);
  const outputMarkdownPath = path.resolve(options.outputMarkdownPath);

  const verifyLiteSummary = readJsonRequired(verifyLiteSummaryPath, 'verify-lite summary');
  const harnessHealth = readJsonRequired(harnessHealthPath, 'harness-health');
  const changePackage = readJsonRequired(changePackagePath, 'change-package');
  const contextPackSuggestions = contextPackSuggestionsPath
    ? readJsonOptional(contextPackSuggestionsPath, 'context-pack suggestions')
    : null;

  const artifact = buildHookFeedbackArtifact({
    verifyLiteSummary,
    harnessHealth,
    changePackage,
    contextPackSuggestions,
    source: {
      verifyLiteSummaryPath: path.relative(process.cwd(), verifyLiteSummaryPath) || path.basename(verifyLiteSummaryPath),
      harnessHealthPath: path.relative(process.cwd(), harnessHealthPath) || path.basename(harnessHealthPath),
      changePackagePath: path.relative(process.cwd(), changePackagePath) || path.basename(changePackagePath),
      contextPackSuggestionsPath: contextPackSuggestions
        ? path.relative(process.cwd(), contextPackSuggestionsPath) || path.basename(contextPackSuggestionsPath)
        : null,
    },
  });

  ensureParentDir(outputJsonPath);
  ensureParentDir(outputMarkdownPath);
  fs.writeFileSync(outputJsonPath, `${JSON.stringify(artifact, null, 2)}\n`);
  fs.writeFileSync(outputMarkdownPath, renderMarkdown(artifact));
  process.stdout.write(`[hook-feedback] report(json): ${outputJsonPath}\n`);
  process.stdout.write(`[hook-feedback] report(md): ${outputMarkdownPath}\n`);
  return { exitCode: 0, artifact };
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  try {
    const result = run(process.argv);
    if (result.exitCode !== 0) {
      process.exitCode = result.exitCode;
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`[hook-feedback] ${message}\n`);
    process.exitCode = 1;
  }
}
