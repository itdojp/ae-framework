#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const DEFAULT_VERIFY_LITE_SUMMARY_PATH = 'artifacts/verify-lite/verify-lite-run-summary.json';
const DEFAULT_HARNESS_HEALTH_PATH = 'artifacts/ci/harness-health.json';
const DEFAULT_CHANGE_PACKAGE_PATH = 'artifacts/change-package/change-package.json';
const DEFAULT_CONTEXT_PACK_SUGGESTIONS_PATH = 'artifacts/context-pack/context-pack-suggestions.json';
const DEFAULT_ASSURANCE_SUMMARY_PATH = 'artifacts/assurance/assurance-summary.json';
const DEFAULT_UI_E2E_SUMMARY_PATH = 'artifacts/e2e/ui-e2e-summary.json';
const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/agents/hook-feedback.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/agents/hook-feedback.md';
const FALLBACK_REPRO_COMMAND = 'pnpm run verify:lite';
const HARNESS_HEALTH_REPRO_COMMAND = 'node scripts/ci/build-harness-health.mjs';
const CHANGE_PACKAGE_REPRO_COMMAND = 'pnpm run change-package:generate';
const ASSURANCE_REPRO_COMMAND = 'pnpm run verify:assurance';
const UI_E2E_REPRO_COMMAND = 'pnpm run ui-e2e:semantic';

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

function summarizeAssuranceSummary(assuranceSummary) {
  const summary = assuranceSummary && typeof assuranceSummary === 'object' ? assuranceSummary.summary ?? {} : {};
  const warningClaims = Number.isFinite(summary.warningClaims) ? Number(summary.warningClaims) : 0;
  const warningCount = Number.isFinite(summary.warningCount) ? Number(summary.warningCount) : 0;
  const missingLanes = Number.isFinite(summary.claimsMissingRequiredLanes)
    ? Number(summary.claimsMissingRequiredLanes)
    : 0;
  const missingEvidenceKinds = Number.isFinite(summary.claimsMissingRequiredEvidenceKinds)
    ? Number(summary.claimsMissingRequiredEvidenceKinds)
    : 0;
  const unlinkedCounterexamples = Number.isFinite(summary.unlinkedCounterexamples)
    ? Number(summary.unlinkedCounterexamples)
    : 0;
  const openCounterexamples = Array.isArray(assuranceSummary?.claims)
    ? assuranceSummary.claims.reduce((total, claim) => {
      if (!claim || typeof claim !== 'object') {
        return total;
      }
      const open = Number.isFinite(claim?.counterexamples?.open) ? Number(claim.counterexamples.open) : 0;
      return total + open;
    }, 0)
    : 0;

  return {
    warningClaims,
    warningCount,
    missingLanes,
    missingEvidenceKinds,
    unlinkedCounterexamples,
    openCounterexamples,
    hasWarnings:
      warningClaims > 0
      || warningCount > 0
      || missingLanes > 0
      || missingEvidenceKinds > 0
      || unlinkedCounterexamples > 0
      || openCounterexamples > 0,
  };
}

function summarizeUiE2E(uiE2ESummary) {
  const status = typeof uiE2ESummary?.status === 'string' ? uiE2ESummary.status : null;
  const scenarios = Array.isArray(uiE2ESummary?.scenarios) ? uiE2ESummary.scenarios : [];
  const failedScenarioIds = scenarios
    .filter((scenario) => scenario?.status === 'fail')
    .map((scenario) => (typeof scenario?.id === 'string' ? scenario.id.trim() : ''))
    .filter(Boolean);

  return {
    status,
    failedScenarioIds,
    hasIssues: status === 'warn' || status === 'error' || failedScenarioIds.length > 0,
  };
}

function summarizeMissingCoreArtifacts({ harnessHealth, changePackage }) {
  const missing = [];
  if (!harnessHealth) {
    missing.push('harness-health');
  }
  if (!changePackage) {
    missing.push('change-package');
  }
  return missing;
}

function deriveStatus({ harnessHealth, verifyLiteSummary, changePackage, contextPackSuggestions, assuranceSummary, uiE2ESummary }) {
  const verifySummary = summarizeVerifyLite(verifyLiteSummary);
  const missingCoreArtifacts = summarizeMissingCoreArtifacts({ harnessHealth, changePackage });
  const assurance = summarizeAssuranceSummary(assuranceSummary);
  const uiE2E = summarizeUiE2E(uiE2ESummary);
  const severity = typeof harnessHealth?.severity === 'string' ? harnessHealth.severity : 'ok';
  const exceptionCount = Array.isArray(changePackage?.exceptions) ? changePackage.exceptions.length : 0;
  const suggestionCount = Array.isArray(contextPackSuggestions?.recommendedContextChanges)
    ? contextPackSuggestions.recommendedContextChanges.length
    : 0;
  const contextStatus = typeof contextPackSuggestions?.status === 'string' ? contextPackSuggestions.status : 'pass';

  if (severity === 'critical' || verifySummary.failingSteps.length > 0) {
    return 'blocked';
  }
  if (
    missingCoreArtifacts.length > 0
    || severity === 'warn'
    || verifySummary.pendingSteps.length > 0
    || exceptionCount > 0
    || (suggestionCount > 0 && contextStatus !== 'pass')
    || assurance.hasWarnings
    || uiE2E.hasIssues
  ) {
    return 'warn';
  }
  return 'ok';
}

function buildBlockingReasons({
  verifyLiteSummary,
  harnessHealth,
  changePackage,
  contextPackSuggestions,
  assuranceSummary,
  uiE2ESummary,
}) {
  const verifySummary = summarizeVerifyLite(verifyLiteSummary);
  const missingCoreArtifacts = summarizeMissingCoreArtifacts({ harnessHealth, changePackage });
  const assurance = summarizeAssuranceSummary(assuranceSummary);
  const uiE2E = summarizeUiE2E(uiE2ESummary);
  const reasons = [];

  for (const artifactName of missingCoreArtifacts) {
    reasons.push(`Missing artifact: ${artifactName}`);
  }
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
  if (assurance.hasWarnings) {
    reasons.push(
      `Assurance summary warnings: warningClaims=${assurance.warningClaims}, `
        + `warningCount=${assurance.warningCount}, missingLanes=${assurance.missingLanes}, `
        + `missingEvidenceKinds=${assurance.missingEvidenceKinds}, unlinkedCounterexamples=${assurance.unlinkedCounterexamples}, `
        + `openCounterexamples=${assurance.openCounterexamples}`,
    );
  }
  if (uiE2E.hasIssues) {
    const scenarioSummary = uiE2E.failedScenarioIds.length > 0
      ? ` failed scenarios: ${uiE2E.failedScenarioIds.join(', ')}`
      : '';
    reasons.push(`UI semantic E2E status=${uiE2E.status ?? 'unknown'}.${scenarioSummary}`.trim());
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

function buildNextActions({
  status,
  verifyLiteSummary,
  harnessHealth,
  changePackage,
  contextPackSuggestions,
  assuranceSummary,
  uiE2ESummary,
}) {
  const verifySummary = summarizeVerifyLite(verifyLiteSummary);
  const missingCoreArtifacts = summarizeMissingCoreArtifacts({ harnessHealth, changePackage });
  const assurance = summarizeAssuranceSummary(assuranceSummary);
  const uiE2E = summarizeUiE2E(uiE2ESummary);
  const actions = [];

  if (missingCoreArtifacts.includes('harness-health')) {
    actions.push(
      `Generate \`artifacts/ci/harness-health.json\` with \`${HARNESS_HEALTH_REPRO_COMMAND}\` when gate-level guidance is needed.`,
    );
  }
  if (missingCoreArtifacts.includes('change-package')) {
    actions.push(
      `Generate \`artifacts/change-package/change-package.json\` with \`${CHANGE_PACKAGE_REPRO_COMMAND}\` when risk/evidence packaging is needed.`,
    );
  }
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
  if (assurance.hasWarnings) {
    actions.push(
      `Run \`${ASSURANCE_REPRO_COMMAND}\` and resolve assurance warnings `
        + `(warningClaims=${assurance.warningClaims}, missingLanes=${assurance.missingLanes}, `
        + `missingEvidenceKinds=${assurance.missingEvidenceKinds}, openCounterexamples=${assurance.openCounterexamples}).`,
    );
  }
  if (uiE2E.hasIssues) {
    const scenarioSummary = uiE2E.failedScenarioIds.length > 0
      ? ` for scenarios: ${uiE2E.failedScenarioIds.join(', ')}`
      : '';
    actions.push(`Run \`${UI_E2E_REPRO_COMMAND}\` and inspect UI semantic E2E evidence${scenarioSummary}.`);
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

function buildReproCommands({ changePackage, harnessHealth, contextPackSuggestions, assuranceSummary, uiE2ESummary }) {
  const missingCoreArtifacts = summarizeMissingCoreArtifacts({ harnessHealth, changePackage });
  const assurance = summarizeAssuranceSummary(assuranceSummary);
  const uiE2E = summarizeUiE2E(uiE2ESummary);
  const commands = uniqueNonEmpty([
    ...(missingCoreArtifacts.includes('harness-health') ? [HARNESS_HEALTH_REPRO_COMMAND] : []),
    ...(missingCoreArtifacts.includes('change-package') ? [CHANGE_PACKAGE_REPRO_COMMAND] : []),
    ...(Array.isArray(changePackage?.reproducibility?.commands) ? changePackage.reproducibility.commands : []),
    ...(Array.isArray(harnessHealth?.reproducibleHints)
      ? harnessHealth.reproducibleHints.map((hint) => hint?.command)
      : []),
    ...(Array.isArray(harnessHealth?.recommendedContextChanges)
      ? harnessHealth.recommendedContextChanges.map((change) => change?.suggestedCommand)
      : []),
    ...(Array.isArray(contextPackSuggestions?.recommendedContextChanges)
      ? contextPackSuggestions.recommendedContextChanges.map((change) => change?.suggestedCommand)
      : []),
    ...(assurance.hasWarnings ? [ASSURANCE_REPRO_COMMAND] : []),
    ...(uiE2E.hasIssues ? [UI_E2E_REPRO_COMMAND] : []),
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
  const existing = items.find((candidate) => candidate.path === item.path);
  if (existing) {
    if ((!existing.id || existing.id === 'evidence') && typeof item.id === 'string' && item.id.trim()) {
      existing.id = item.id.trim();
    }
    if (
      (!existing.description || existing.description === 'referenced evidence')
      && typeof item.description === 'string'
      && item.description.trim()
    ) {
      existing.description = item.description.trim();
    }
    if (typeof item.present === 'boolean') {
      existing.present = Boolean(existing.present) || item.present;
    }
    if (typeof item.status === 'string' && item.status.trim()) {
      existing.status = item.status.trim();
    }
    return;
  }
  items.push(item);
}

function buildEvidence({
  verifyLiteSummaryPath,
  harnessHealthPath,
  changePackagePath,
  contextPackSuggestionsPath,
  assuranceSummaryPath,
  uiE2ESummaryPath,
  verifyLiteSummary,
  changePackage,
  harnessHealth,
  contextPackSuggestions,
  assuranceSummary,
  uiE2ESummary,
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
    present: Boolean(harnessHealth),
    status: typeof harnessHealth?.severity === 'string' ? harnessHealth.severity : 'missing',
  });
  addEvidenceItem(items, {
    id: 'changePackage',
    path: changePackagePath,
    description: 'change package evidence bundle',
    present: Boolean(changePackage),
    status: typeof changePackage?.risk?.selected === 'string' ? changePackage.risk.selected : 'missing',
  });
  if (contextPackSuggestionsPath) {
    addEvidenceItem(items, {
      id: 'contextPackSuggestions',
      path: contextPackSuggestionsPath,
      description: 'context-pack suggestion summary',
      present: Boolean(contextPackSuggestions),
      status: typeof contextPackSuggestions?.status === 'string' ? contextPackSuggestions.status : 'missing',
    });
  }
  if (assuranceSummaryPath) {
    const assurance = summarizeAssuranceSummary(assuranceSummary);
    addEvidenceItem(items, {
      id: 'assuranceSummary',
      path: assuranceSummaryPath,
      description: 'assurance summary',
      present: Boolean(assuranceSummary),
      status: assuranceSummary ? (assurance.hasWarnings ? 'warn' : 'ok') : 'missing',
    });
  }
  if (uiE2ESummaryPath) {
    const uiE2E = summarizeUiE2E(uiE2ESummary);
    addEvidenceItem(items, {
      id: 'uiE2ESummary',
      path: uiE2ESummaryPath,
      description: 'UI semantic E2E summary',
      present: Boolean(uiE2ESummary),
      status: uiE2ESummary ? uiE2E.status : 'missing',
    });
  }

  return items;
}

export function buildHookFeedbackArtifact({
  verifyLiteSummary,
  harnessHealth,
  changePackage,
  contextPackSuggestions,
  assuranceSummary,
  uiE2ESummary,
  source,
  evidenceSource = source,
  now = new Date().toISOString(),
}) {
  const status = deriveStatus({
    verifyLiteSummary,
    harnessHealth,
    changePackage,
    contextPackSuggestions,
    assuranceSummary,
    uiE2ESummary,
  });
  return {
    schemaVersion: 'hook-feedback/v1',
    generatedAt: now,
    status,
    blockingReasons: buildBlockingReasons({
      verifyLiteSummary,
      harnessHealth,
      changePackage,
      contextPackSuggestions,
      assuranceSummary,
      uiE2ESummary,
    }),
    nextActions: buildNextActions({
      status,
      verifyLiteSummary,
      harnessHealth,
      changePackage,
      contextPackSuggestions,
      assuranceSummary,
      uiE2ESummary,
    }),
    reproCommands: buildReproCommands({
      changePackage,
      harnessHealth,
      contextPackSuggestions,
      assuranceSummary,
      uiE2ESummary,
    }),
    evidence: buildEvidence({
      verifyLiteSummaryPath: evidenceSource.verifyLiteSummaryPath,
      harnessHealthPath: evidenceSource.harnessHealthPath,
      changePackagePath: evidenceSource.changePackagePath,
      contextPackSuggestionsPath: evidenceSource.contextPackSuggestionsPath,
      assuranceSummaryPath: evidenceSource.assuranceSummaryPath,
      uiE2ESummaryPath: evidenceSource.uiE2ESummaryPath,
      verifyLiteSummary,
      changePackage,
      harnessHealth,
      contextPackSuggestions,
      assuranceSummary,
      uiE2ESummary,
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
  lines.push(`- harness-health: \`${artifact.source.harnessHealthPath ?? 'n/a'}\``);
  lines.push(`- change-package: \`${artifact.source.changePackagePath ?? 'n/a'}\``);
  lines.push(`- context-pack suggestions: \`${artifact.source.contextPackSuggestionsPath ?? 'n/a'}\``);
  lines.push(`- assurance-summary: \`${artifact.source.assuranceSummaryPath ?? 'n/a'}\``);
  lines.push(`- ui-e2e-summary: \`${artifact.source.uiE2ESummaryPath ?? 'n/a'}\``);
  return `${lines.join('\n')}\n`;
}

export function parseArgs(argv = process.argv) {
  const options = {
    verifyLiteSummaryPath: DEFAULT_VERIFY_LITE_SUMMARY_PATH,
    harnessHealthPath: DEFAULT_HARNESS_HEALTH_PATH,
    changePackagePath: DEFAULT_CHANGE_PACKAGE_PATH,
    contextPackSuggestionsPath: DEFAULT_CONTEXT_PACK_SUGGESTIONS_PATH,
    assuranceSummaryPath: DEFAULT_ASSURANCE_SUMMARY_PATH,
    uiE2ESummaryPath: DEFAULT_UI_E2E_SUMMARY_PATH,
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
    if (arg === '--assurance-summary') {
      options.assuranceSummaryPath = readValue(next, '--assurance-summary');
      index += 1;
      continue;
    }
    if (arg.startsWith('--assurance-summary=')) {
      options.assuranceSummaryPath = arg.slice('--assurance-summary='.length);
      continue;
    }
    if (arg === '--ui-e2e-summary') {
      options.uiE2ESummaryPath = readValue(next, '--ui-e2e-summary');
      index += 1;
      continue;
    }
    if (arg.startsWith('--ui-e2e-summary=')) {
      options.uiE2ESummaryPath = arg.slice('--ui-e2e-summary='.length);
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
      + `  --harness-health <path>            Optional harness health path (default: ${DEFAULT_HARNESS_HEALTH_PATH})\n`
      + `  --change-package <path>            Optional Change Package path (default: ${DEFAULT_CHANGE_PACKAGE_PATH})\n`
      + `  --context-pack-suggestions <path>  Optional Context Pack suggestions path (default: ${DEFAULT_CONTEXT_PACK_SUGGESTIONS_PATH})\n`
      + `  --assurance-summary <path>         Optional assurance summary path (default: ${DEFAULT_ASSURANCE_SUMMARY_PATH})\n`
      + `  --ui-e2e-summary <path>            Optional UI E2E summary path (default: ${DEFAULT_UI_E2E_SUMMARY_PATH})\n`
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
  const assuranceSummaryPath = options.assuranceSummaryPath
    ? path.resolve(options.assuranceSummaryPath)
    : null;
  const uiE2ESummaryPath = options.uiE2ESummaryPath
    ? path.resolve(options.uiE2ESummaryPath)
    : null;
  const outputJsonPath = path.resolve(options.outputJsonPath);
  const outputMarkdownPath = path.resolve(options.outputMarkdownPath);

  const verifyLiteSummary = readJsonRequired(verifyLiteSummaryPath, 'verify-lite summary');
  const harnessHealth = readJsonOptional(harnessHealthPath, 'harness-health');
  const changePackage = readJsonOptional(changePackagePath, 'change-package');
  const contextPackSuggestions = contextPackSuggestionsPath
    ? readJsonOptional(contextPackSuggestionsPath, 'context-pack suggestions')
    : null;
  const assuranceSummary = assuranceSummaryPath
    ? readJsonOptional(assuranceSummaryPath, 'assurance summary')
    : null;
  const uiE2ESummary = uiE2ESummaryPath
    ? readJsonOptional(uiE2ESummaryPath, 'ui-e2e summary')
    : null;

  const artifact = buildHookFeedbackArtifact({
    verifyLiteSummary,
    harnessHealth,
    changePackage,
    contextPackSuggestions,
    assuranceSummary,
    uiE2ESummary,
    source: {
      verifyLiteSummaryPath: path.relative(process.cwd(), verifyLiteSummaryPath) || path.basename(verifyLiteSummaryPath),
      harnessHealthPath: harnessHealth
        ? path.relative(process.cwd(), harnessHealthPath) || path.basename(harnessHealthPath)
        : null,
      changePackagePath: changePackage
        ? path.relative(process.cwd(), changePackagePath) || path.basename(changePackagePath)
        : null,
      contextPackSuggestionsPath: contextPackSuggestions
        ? path.relative(process.cwd(), contextPackSuggestionsPath) || path.basename(contextPackSuggestionsPath)
        : null,
      assuranceSummaryPath: assuranceSummary
        ? path.relative(process.cwd(), assuranceSummaryPath) || path.basename(assuranceSummaryPath)
        : null,
      uiE2ESummaryPath: uiE2ESummary
        ? path.relative(process.cwd(), uiE2ESummaryPath) || path.basename(uiE2ESummaryPath)
        : null,
    },
    evidenceSource: {
      verifyLiteSummaryPath: path.relative(process.cwd(), verifyLiteSummaryPath) || path.basename(verifyLiteSummaryPath),
      harnessHealthPath: path.relative(process.cwd(), harnessHealthPath) || path.basename(harnessHealthPath),
      changePackagePath: path.relative(process.cwd(), changePackagePath) || path.basename(changePackagePath),
      contextPackSuggestionsPath: contextPackSuggestionsPath
        ? path.relative(process.cwd(), contextPackSuggestionsPath) || path.basename(contextPackSuggestionsPath)
        : null,
      assuranceSummaryPath: assuranceSummaryPath
        ? path.relative(process.cwd(), assuranceSummaryPath) || path.basename(assuranceSummaryPath)
        : null,
      uiE2ESummaryPath: uiE2ESummaryPath
        ? path.relative(process.cwd(), uiE2ESummaryPath) || path.basename(uiE2ESummaryPath)
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
