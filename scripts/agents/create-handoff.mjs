#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { buildHookFeedbackArtifact } from './build-hook-feedback.mjs';

const DEFAULT_HOOK_FEEDBACK_PATH = 'artifacts/agents/hook-feedback.json';
const DEFAULT_VERIFY_LITE_SUMMARY_PATH = 'artifacts/verify-lite/verify-lite-run-summary.json';
const DEFAULT_HARNESS_HEALTH_PATH = 'artifacts/ci/harness-health.json';
const DEFAULT_CHANGE_PACKAGE_PATH = 'artifacts/change-package/change-package.json';
const DEFAULT_CONTEXT_PACK_SUGGESTIONS_PATH = 'artifacts/context-pack/context-pack-suggestions.json';
const DEFAULT_ASSURANCE_SUMMARY_PATH = 'artifacts/assurance/assurance-summary.json';
const DEFAULT_UI_E2E_SUMMARY_PATH = 'artifacts/e2e/ui-e2e-summary.json';
const DEFAULT_POLICY_GATE_SUMMARY_PATH = 'artifacts/ci/policy-gate-summary.json';
const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/handoff/ae-handoff.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/handoff/ae-handoff.md';
const DEFAULT_SCHEMA_PATH = 'schema/ae-handoff.schema.json';
const FALLBACK_COMMAND = 'pnpm -s run verify:lite';

function readRequiredValue(argv, index, option) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`missing value for ${option}`);
  }
  return next;
}

function ensureParentDir(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

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

function normalizeOptionalText(value) {
  if (typeof value !== 'string') {
    return null;
  }
  const normalized = value.trim();
  return normalized || null;
}

function maxBacktickRun(text) {
  const input = typeof text === 'string' ? text : String(text ?? '');
  const matches = input.match(/`+/g) ?? [];
  return matches.reduce((max, run) => Math.max(max, run.length), 0);
}

function wrapInlineCode(text) {
  const content = typeof text === 'string' ? text : String(text ?? '');
  const fence = '`'.repeat(Math.max(1, maxBacktickRun(content) + 1));
  return `${fence}${content}${fence}`;
}

function renderFencedCodeBlock(language, text) {
  const content = typeof text === 'string' ? text : String(text ?? '');
  const fence = '`'.repeat(Math.max(3, maxBacktickRun(content) + 1));
  return `${fence}${language}\n${content}\n${fence}`;
}

function relativeOrNull(absolutePath) {
  if (!absolutePath) {
    return null;
  }
  const relativePath = path.relative(process.cwd(), absolutePath);
  return relativePath || path.basename(absolutePath);
}

function readJsonOptional(filePath, label) {
  if (!filePath || !fs.existsSync(filePath)) {
    return null;
  }
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`${label} could not be read: ${filePath} (${message})`);
  }
}

function readSchema(schemaPath) {
  if (!fs.existsSync(schemaPath)) {
    throw new Error(`schema not found: ${schemaPath}`);
  }
  try {
    return JSON.parse(fs.readFileSync(schemaPath, 'utf8'));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`schema could not be read: ${schemaPath} (${message})`);
  }
}

function summarizeVerifyLite(verifyLiteSummary) {
  const steps = verifyLiteSummary && typeof verifyLiteSummary === 'object'
    ? verifyLiteSummary.steps ?? {}
    : {};
  const failing = [];
  const pending = [];

  for (const [stepName, payload] of Object.entries(steps)) {
    const status = typeof payload?.status === 'string' ? payload.status : 'unknown';
    if (status === 'failure') {
      failing.push(stepName);
    } else if (status === 'pending' || status === 'unknown') {
      pending.push(stepName);
    }
  }

  return {
    failing: uniqueNonEmpty(failing),
    pending: uniqueNonEmpty(pending),
  };
}

function summarizeAssurance(assuranceSummary) {
  const summary = assuranceSummary && typeof assuranceSummary === 'object'
    ? assuranceSummary.summary ?? {}
    : {};
  const warningClaims = Number.isFinite(summary.warningClaims) ? Number(summary.warningClaims) : 0;
  const missingLanes = Number.isFinite(summary.claimsMissingRequiredLanes)
    ? Number(summary.claimsMissingRequiredLanes)
    : 0;
  const missingEvidenceKinds = Number.isFinite(summary.claimsMissingRequiredEvidenceKinds)
    ? Number(summary.claimsMissingRequiredEvidenceKinds)
    : 0;
  const unlinkedCounterexamples = Number.isFinite(summary.unlinkedCounterexamples)
    ? Number(summary.unlinkedCounterexamples)
    : 0;
  const warningCount = Number.isFinite(summary.warningCount) ? Number(summary.warningCount) : 0;

  return {
    warningClaims,
    missingLanes,
    missingEvidenceKinds,
    unlinkedCounterexamples,
    warningCount,
    hasWarnings:
      warningClaims > 0
      || missingLanes > 0
      || missingEvidenceKinds > 0
      || unlinkedCounterexamples > 0
      || warningCount > 0,
  };
}

function summarizePolicyGate(policyGateSummary) {
  const evaluation = policyGateSummary && typeof policyGateSummary === 'object'
    ? policyGateSummary.evaluation ?? {}
    : {};
  const errors = Array.isArray(evaluation.errors) ? uniqueNonEmpty(evaluation.errors) : [];
  const warnings = Array.isArray(evaluation.warnings) ? uniqueNonEmpty(evaluation.warnings) : [];
  const ok = evaluation.ok === true;
  return { ok, errors, warnings };
}

function parseAction(action) {
  const text = typeof action === 'string' ? action.trim() : '';
  if (!text) {
    return null;
  }

  const commandMatches = Array.from(text.matchAll(/`([^`]+)`/g));
  const commandMatch = commandMatches.at(-1);
  return {
    summary: text.replace(/`([^`]+)`/g, '$1').trim(),
    command: commandMatch?.[1]?.trim() ?? null,
  };
}

function classifyBlockerKind(reason) {
  if (/approval|review|human|operator/i.test(reason)) {
    return 'human';
  }
  if (/verify|policy|artifact|assurance|counterexample|e2e|build|lint|test|harness/i.test(reason)) {
    return 'ci';
  }
  return 'unknown';
}

function parseBlocker(blocker) {
  if (typeof blocker !== 'string') {
    return null;
  }
  const [summaryPart, kindPart] = blocker.split('::');
  const summary = summaryPart?.trim();
  if (!summary) {
    return null;
  }
  const explicitKind = kindPart?.trim();
  const kind = ['human', 'ci', 'external', 'unknown'].includes(explicitKind)
    ? explicitKind
    : classifyBlockerKind(summary);
  return { summary, kind };
}

function parseArtifactEntry(entry) {
  if (typeof entry !== 'string') {
    return null;
  }
  const [rawPath, ...descriptionParts] = entry.split('::');
  const artifactPath = rawPath?.trim();
  if (!artifactPath) {
    return null;
  }
  const description = descriptionParts.join('::').trim();
  return {
    path: artifactPath,
    description: description || null,
  };
}

function addArtifact(artifacts, artifact) {
  if (!artifact?.path) {
    return;
  }
  if (artifacts.some((entry) => entry.path === artifact.path)) {
    return;
  }
  artifacts.push(artifact);
}

function buildCurrentStatus({ hookFeedback, verifyLiteSummary, assuranceSummary, policyGateSummary }) {
  const status = typeof hookFeedback?.status === 'string' ? hookFeedback.status : null;
  const blockingReasons = Array.isArray(hookFeedback?.blockingReasons)
    ? uniqueNonEmpty(hookFeedback.blockingReasons)
    : [];
  const verifyLite = summarizeVerifyLite(verifyLiteSummary);
  const assurance = summarizeAssurance(assuranceSummary);
  const policyGate = summarizePolicyGate(policyGateSummary);

  if (status === 'blocked' || verifyLite.failing.length > 0 || policyGate.errors.length > 0) {
    if (policyGate.errors.length > 0) {
      return `Blocked. ${policyGate.errors.slice(0, 2).join(' / ')}`;
    }
    const highlights = blockingReasons.slice(0, 2).join(' / ');
    return highlights ? `Blocked. ${highlights}` : 'Blocked. See current blocking reasons.';
  }
  if (status === 'warn' || verifyLite.pending.length > 0 || assurance.hasWarnings) {
    const highlights = blockingReasons.slice(0, 2).join(' / ');
    return highlights ? `Warnings remain. ${highlights}` : 'Warnings remain. Review evidence before handoff.';
  }
  if (status === 'ok') {
    return 'Ready for review based on current evidence.';
  }
  return 'Current status is derived from the available artifacts only.';
}

function buildNextActions({ nextActions, commandsRun, verifyLiteSummary, assuranceSummary, policyGateSummary }) {
  const parsed = uniqueNonEmpty(nextActions)
    .map(parseAction)
    .filter(Boolean)
    .slice(0, 10)
    .map((action, index) => ({
      order: index + 1,
      summary: action.summary,
      command: action.command,
    }));

  if (parsed.length > 0) {
    return parsed;
  }

  const verifyLite = summarizeVerifyLite(verifyLiteSummary);
  if (verifyLite.failing.length > 0) {
    return [{
      order: 1,
      summary: `Fix failing verify-lite steps: ${verifyLite.failing.join(', ')}`,
      command: commandsRun[0] ?? FALLBACK_COMMAND,
    }];
  }

  const policyGate = summarizePolicyGate(policyGateSummary);
  if (policyGate.errors.length > 0) {
    return [{
      order: 1,
      summary: 'Resolve policy-gate errors before requesting review.',
      command: 'gh pr checks --required',
    }];
  }

  const assurance = summarizeAssurance(assuranceSummary);
  if (assurance.hasWarnings) {
    return [{
      order: 1,
      summary: 'Resolve assurance warnings before requesting review or handoff completion.',
      command: 'pnpm -s run verify:assurance',
    }];
  }

  return [{
    order: 1,
    summary: 'Reconfirm the current state before requesting review or continuation.',
    command: commandsRun[commandsRun.length - 1] ?? FALLBACK_COMMAND,
  }];
}

function buildArtifacts({
  hookFeedbackPath,
  hookFeedback,
  verifyLiteSummaryPath,
  assuranceSummaryPath,
  changePackagePath,
  policyGateSummaryPath,
  manualArtifacts,
}) {
  const artifacts = [];

  if (hookFeedbackPath) {
    addArtifact(artifacts, {
      path: hookFeedbackPath,
      description: 'hook feedback summary',
    });
  }

  if (Array.isArray(hookFeedback?.evidence)) {
    for (const evidence of hookFeedback.evidence) {
      if (evidence?.present === false) {
        continue;
      }
      if (typeof evidence?.path !== 'string' || !evidence.path.trim()) {
        continue;
      }
      addArtifact(artifacts, {
        path: evidence.path.trim(),
        description:
          typeof evidence?.description === 'string' && evidence.description.trim()
            ? evidence.description.trim()
            : null,
      });
    }
  }

  if (verifyLiteSummaryPath) {
    addArtifact(artifacts, { path: verifyLiteSummaryPath, description: 'verify-lite run summary' });
  }
  if (assuranceSummaryPath) {
    addArtifact(artifacts, { path: assuranceSummaryPath, description: 'assurance summary' });
  }
  if (changePackagePath) {
    addArtifact(artifacts, { path: changePackagePath, description: 'change package' });
  }
  if (policyGateSummaryPath) {
    addArtifact(artifacts, { path: policyGateSummaryPath, description: 'policy-gate summary' });
  }
  for (const entry of manualArtifacts) {
    addArtifact(artifacts, parseArtifactEntry(entry));
  }

  return artifacts;
}

function buildBlockers({ blockingReasons, assuranceSummary, policyGateSummary, manualBlockers }) {
  const blockers = [];
  const add = (blocker) => {
    if (!blocker?.summary) {
      return;
    }
    if (!blockers.some((entry) => entry.summary === blocker.summary)) {
      blockers.push(blocker);
    }
  };

  for (const reason of uniqueNonEmpty(blockingReasons)) {
    add(parseBlocker(reason));
  }

  const assurance = summarizeAssurance(assuranceSummary);
  if (assurance.hasWarnings) {
    add({
      summary:
        `assurance warnings remain (warningClaims=${assurance.warningClaims}, missingLanes=${assurance.missingLanes}, missingEvidenceKinds=${assurance.missingEvidenceKinds}, unlinkedCounterexamples=${assurance.unlinkedCounterexamples})`,
      kind: 'ci',
    });
  }

  const policyGate = summarizePolicyGate(policyGateSummary);
  for (const error of policyGate.errors) {
    add({ summary: `policy-gate: ${error}`, kind: 'ci' });
  }

  for (const entry of manualBlockers) {
    add(parseBlocker(entry));
  }

  return blockers;
}

export function renderMarkdown(handoff) {
  const artifactList = handoff.artifacts.length > 0
    ? handoff.artifacts.map((artifact) => {
        const description = artifact.description ? ` (${artifact.description})` : '';
        return `${wrapInlineCode(artifact.path)}${description}`;
      }).join(', ')
    : 'n/a';
  const blockerList = handoff.blockers.length > 0
    ? handoff.blockers.map((blocker) => `${blocker.summary}${blocker.kind ? ` [${blocker.kind}]` : ''}`).join('; ')
    : 'none';

  const lines = [
    '## AE-HANDOFF',
    `- Goal: ${handoff.goal}`,
    `- Current status: ${handoff.currentStatus}`,
    '- Next actions:',
  ];

  for (const action of handoff.nextActions) {
    const commandSuffix = action.command ? ` — ${wrapInlineCode(action.command)}` : '';
    lines.push(`  ${action.order}. ${action.summary}${commandSuffix}`);
  }

  lines.push(`- Commands run: ${handoff.commandsRun.map((command) => wrapInlineCode(command)).join(', ')}`);
  lines.push(`- Artifacts: ${artifactList}`);
  lines.push(`- Risks / Rollback note: ${handoff.risksRollbackNote ?? 'n/a'}`);
  lines.push(`- Blockers: ${blockerList}`);
  lines.push(`- Change Package: ${handoff.changePackageRef ?? 'n/a'}`);
  lines.push('', renderFencedCodeBlock('json', JSON.stringify(handoff, null, 2)), '');
  return `${lines.join('\n')}\n`;
}

function printHelp() {
  process.stdout.write(
    'Build deterministic AE-HANDOFF sidecars from existing evidence.\n\n'
      + 'Usage:\n'
      + '  node scripts/agents/create-handoff.mjs --goal <text> [options]\n\n'
      + 'Options:\n'
      + `  --hook-feedback <path>           Existing hook-feedback JSON path (default: ${DEFAULT_HOOK_FEEDBACK_PATH})\n`
      + `  --verify-lite-summary <path>     Verify Lite summary path used when hook-feedback must be derived (default: ${DEFAULT_VERIFY_LITE_SUMMARY_PATH})\n`
      + `  --harness-health <path>          Optional harness health path (default: ${DEFAULT_HARNESS_HEALTH_PATH})\n`
      + `  --change-package <path>          Optional change package path (default: ${DEFAULT_CHANGE_PACKAGE_PATH})\n`
      + `  --context-pack-suggestions <path> Optional context-pack suggestions path (default: ${DEFAULT_CONTEXT_PACK_SUGGESTIONS_PATH})\n`
      + `  --assurance-summary <path>       Optional assurance summary path (default: ${DEFAULT_ASSURANCE_SUMMARY_PATH})\n`
      + `  --ui-e2e-summary <path>          Optional UI E2E summary path (default: ${DEFAULT_UI_E2E_SUMMARY_PATH})\n`
      + `  --policy-gate-summary <path>     Optional policy-gate summary path (default: ${DEFAULT_POLICY_GATE_SUMMARY_PATH})\n`
      + `  --output-json <path>             Output JSON path (default: ${DEFAULT_OUTPUT_JSON_PATH})\n`
      + `  --output-md <path>               Output Markdown path (default: ${DEFAULT_OUTPUT_MD_PATH})\n`
      + `  --schema <path>                  Schema path for final validation (default: ${DEFAULT_SCHEMA_PATH})\n`
      + '  --goal <text>                    Required handoff goal\n'
      + '  --target <text>                  Optional handoff target\n'
      + '  --current-status <text>          Optional current status override\n'
      + '  --change-package-ref <path>      Optional change package reference override\n'
      + '  --risks-rollback-note <text>     Optional risks / rollback note\n'
      + '  --generated-at <iso8601>         Optional generatedAt override for deterministic tests\n'
      + '  --command-run <cmd>              Repeated; commands already run (falls back to repro commands when omitted)\n'
      + '  --artifact <path[::description]> Repeated; extra artifact entry\n'
      + '  --blocker <summary[::kind]>      Repeated; extra blocker (human|ci|external|unknown)\n'
      + '  --help, -h                       Show help\n',
  );
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    goal: null,
    target: null,
    currentStatus: null,
    changePackageRef: null,
    risksRollbackNote: null,
    generatedAt: null,
    hookFeedbackPath: DEFAULT_HOOK_FEEDBACK_PATH,
    verifyLiteSummaryPath: DEFAULT_VERIFY_LITE_SUMMARY_PATH,
    harnessHealthPath: DEFAULT_HARNESS_HEALTH_PATH,
    changePackagePath: DEFAULT_CHANGE_PACKAGE_PATH,
    contextPackSuggestionsPath: DEFAULT_CONTEXT_PACK_SUGGESTIONS_PATH,
    assuranceSummaryPath: DEFAULT_ASSURANCE_SUMMARY_PATH,
    uiE2ESummaryPath: DEFAULT_UI_E2E_SUMMARY_PATH,
    policyGateSummaryPath: DEFAULT_POLICY_GATE_SUMMARY_PATH,
    outputJsonPath: DEFAULT_OUTPUT_JSON_PATH,
    outputMarkdownPath: DEFAULT_OUTPUT_MD_PATH,
    schemaPath: DEFAULT_SCHEMA_PATH,
    commandsRun: [],
    artifacts: [],
    blockers: [],
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];

    if (arg === '--goal') {
      options.goal = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--target') {
      options.target = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--current-status') {
      options.currentStatus = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--change-package-ref') {
      options.changePackageRef = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--risks-rollback-note') {
      options.risksRollbackNote = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--hook-feedback') {
      options.hookFeedbackPath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--verify-lite-summary') {
      options.verifyLiteSummaryPath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--harness-health') {
      options.harnessHealthPath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--change-package') {
      options.changePackagePath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--context-pack-suggestions') {
      options.contextPackSuggestionsPath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--assurance-summary') {
      options.assuranceSummaryPath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--ui-e2e-summary') {
      options.uiE2ESummaryPath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--policy-gate-summary') {
      options.policyGateSummaryPath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      options.outputJsonPath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMarkdownPath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--schema') {
      options.schemaPath = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--command-run') {
      options.commandsRun.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--artifact') {
      options.artifacts.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--blocker') {
      options.blockers.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  options.goal = normalizeOptionalText(options.goal);
  options.target = normalizeOptionalText(options.target);
  options.currentStatus = normalizeOptionalText(options.currentStatus);
  options.changePackageRef = normalizeOptionalText(options.changePackageRef);
  options.risksRollbackNote = normalizeOptionalText(options.risksRollbackNote);

  if (!options.help && !options.goal) {
    throw new Error('--goal is required');
  }

  return options;
}

function loadHookFeedback(options) {
  const resolvedHookFeedbackPath = path.resolve(options.hookFeedbackPath);
  const existingHookFeedback = readJsonOptional(resolvedHookFeedbackPath, 'hook-feedback');
  if (existingHookFeedback) {
    return {
      hookFeedback: existingHookFeedback,
      hookFeedbackPath: relativeOrNull(resolvedHookFeedbackPath),
      verifyLiteSummaryPath: existingHookFeedback.source?.verifyLiteSummaryPath ?? null,
      assuranceSummaryPath: existingHookFeedback.source?.assuranceSummaryPath ?? null,
      changePackagePath: existingHookFeedback.source?.changePackagePath ?? null,
      policyGateSummaryPath: fs.existsSync(path.resolve(options.policyGateSummaryPath))
        ? relativeOrNull(path.resolve(options.policyGateSummaryPath))
        : null,
      verifyLiteSummary: existingHookFeedback.source?.verifyLiteSummaryPath
        ? readJsonOptional(path.resolve(existingHookFeedback.source.verifyLiteSummaryPath), 'verify-lite summary')
        : null,
      assuranceSummary: existingHookFeedback.source?.assuranceSummaryPath
        ? readJsonOptional(path.resolve(existingHookFeedback.source.assuranceSummaryPath), 'assurance summary')
        : null,
      policyGateSummary: fs.existsSync(path.resolve(options.policyGateSummaryPath))
        ? readJsonOptional(path.resolve(options.policyGateSummaryPath), 'policy-gate summary')
        : null,
    };
  }

  const resolvedVerifyLiteSummaryPath = path.resolve(options.verifyLiteSummaryPath);
  if (!fs.existsSync(resolvedVerifyLiteSummaryPath)) {
    throw new Error(
      `hook-feedback not found at ${resolvedHookFeedbackPath} and verify-lite summary not found at ${resolvedVerifyLiteSummaryPath}`,
    );
  }

  const resolvedHarnessHealthPath = path.resolve(options.harnessHealthPath);
  const resolvedChangePackagePath = path.resolve(options.changePackagePath);
  const resolvedContextPackSuggestionsPath = path.resolve(options.contextPackSuggestionsPath);
  const resolvedAssuranceSummaryPath = path.resolve(options.assuranceSummaryPath);
  const resolvedUiE2ESummaryPath = path.resolve(options.uiE2ESummaryPath);
  const resolvedPolicyGateSummaryPath = path.resolve(options.policyGateSummaryPath);

  const verifyLiteSummary = readJsonOptional(resolvedVerifyLiteSummaryPath, 'verify-lite summary');
  const harnessHealth = readJsonOptional(resolvedHarnessHealthPath, 'harness-health');
  const changePackage = readJsonOptional(resolvedChangePackagePath, 'change-package');
  const contextPackSuggestions = readJsonOptional(resolvedContextPackSuggestionsPath, 'context-pack suggestions');
  const assuranceSummary = readJsonOptional(resolvedAssuranceSummaryPath, 'assurance summary');
  const uiE2ESummary = readJsonOptional(resolvedUiE2ESummaryPath, 'ui-e2e summary');
  const policyGateSummary = readJsonOptional(resolvedPolicyGateSummaryPath, 'policy-gate summary');

  const hookFeedback = buildHookFeedbackArtifact({
    verifyLiteSummary,
    harnessHealth,
    changePackage,
    contextPackSuggestions,
    assuranceSummary,
    uiE2ESummary,
    source: {
      verifyLiteSummaryPath: relativeOrNull(resolvedVerifyLiteSummaryPath),
      harnessHealthPath: harnessHealth ? relativeOrNull(resolvedHarnessHealthPath) : null,
      changePackagePath: changePackage ? relativeOrNull(resolvedChangePackagePath) : null,
      contextPackSuggestionsPath: contextPackSuggestions ? relativeOrNull(resolvedContextPackSuggestionsPath) : null,
      assuranceSummaryPath: assuranceSummary ? relativeOrNull(resolvedAssuranceSummaryPath) : null,
      uiE2ESummaryPath: uiE2ESummary ? relativeOrNull(resolvedUiE2ESummaryPath) : null,
    },
    evidenceSource: {
      verifyLiteSummaryPath: relativeOrNull(resolvedVerifyLiteSummaryPath),
      harnessHealthPath: relativeOrNull(resolvedHarnessHealthPath),
      changePackagePath: relativeOrNull(resolvedChangePackagePath),
      contextPackSuggestionsPath: relativeOrNull(resolvedContextPackSuggestionsPath),
      assuranceSummaryPath: relativeOrNull(resolvedAssuranceSummaryPath),
      uiE2ESummaryPath: relativeOrNull(resolvedUiE2ESummaryPath),
    },
  });

  return {
    hookFeedback,
    hookFeedbackPath: null,
    verifyLiteSummaryPath: relativeOrNull(resolvedVerifyLiteSummaryPath),
    assuranceSummaryPath: assuranceSummary ? relativeOrNull(resolvedAssuranceSummaryPath) : null,
    changePackagePath: changePackage ? relativeOrNull(resolvedChangePackagePath) : null,
    policyGateSummaryPath: policyGateSummary ? relativeOrNull(resolvedPolicyGateSummaryPath) : null,
    verifyLiteSummary,
    assuranceSummary,
    policyGateSummary,
  };
}

export function buildHandoffArtifact({ options, hookFeedbackBundle, now = new Date().toISOString() }) {
  const {
    hookFeedback,
    hookFeedbackPath,
    verifyLiteSummaryPath,
    assuranceSummaryPath,
    changePackagePath,
    policyGateSummaryPath,
    verifyLiteSummary,
    assuranceSummary,
    policyGateSummary,
  } = hookFeedbackBundle;

  const commandsRun = uniqueNonEmpty([
    ...options.commandsRun,
    ...(Array.isArray(hookFeedback?.reproCommands) ? hookFeedback.reproCommands : []),
  ]);
  if (commandsRun.length === 0) {
    commandsRun.push(FALLBACK_COMMAND);
  }

  const blockingReasons = Array.isArray(hookFeedback?.blockingReasons) ? hookFeedback.blockingReasons : [];
  const nextActions = Array.isArray(hookFeedback?.nextActions) ? hookFeedback.nextActions : [];
  const artifacts = buildArtifacts({
    hookFeedbackPath,
    hookFeedback,
    verifyLiteSummaryPath,
    assuranceSummaryPath,
    changePackagePath,
    policyGateSummaryPath,
    manualArtifacts: options.artifacts,
  });
  const blockers = buildBlockers({
    blockingReasons,
    assuranceSummary,
    policyGateSummary,
    manualBlockers: options.blockers,
  });

  if (artifacts.length === 0) {
    throw new Error('at least one artifact is required to build AE-HANDOFF');
  }

  return {
    schemaVersion: 'ae-handoff/v1',
    generatedAt: now,
    handoffTarget: options.target ?? null,
    goal: options.goal,
    currentStatus: (options.currentStatus ?? buildCurrentStatus({
      hookFeedback,
      verifyLiteSummary,
      assuranceSummary,
      policyGateSummary,
    })),
    nextActions: buildNextActions({
      nextActions,
      commandsRun,
      verifyLiteSummary,
      assuranceSummary,
      policyGateSummary,
    }),
    commandsRun,
    artifacts,
    risksRollbackNote: options.risksRollbackNote ?? null,
    blockers,
    changePackageRef: options.changePackageRef ?? changePackagePath ?? null,
  };
}

export function validateHandoffArtifact(handoff, schemaPath = DEFAULT_SCHEMA_PATH) {
  const schema = readSchema(path.resolve(schemaPath));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const valid = validate(handoff);

  if (!valid) {
    const details = (validate.errors ?? [])
      .map((error) => `${error.instancePath || '/'} ${error.message}`)
      .join('; ');
    throw new Error(`schema validation failed: ${details}`);
  }
}

export function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  if (!argvPath) {
    return false;
  }
  return fileURLToPath(importMetaUrl) === path.resolve(argvPath);
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return { exitCode: 0 };
  }

  const hookFeedbackBundle = loadHookFeedback(options);
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const handoff = buildHandoffArtifact({ options, hookFeedbackBundle, now: generatedAt });
  validateHandoffArtifact(handoff, options.schemaPath);

  const outputJsonPath = path.resolve(options.outputJsonPath);
  const outputMarkdownPath = path.resolve(options.outputMarkdownPath);
  ensureParentDir(outputJsonPath);
  ensureParentDir(outputMarkdownPath);

  fs.writeFileSync(outputJsonPath, `${JSON.stringify(handoff, null, 2)}\n`, 'utf8');
  fs.writeFileSync(outputMarkdownPath, renderMarkdown(handoff), 'utf8');
  process.stdout.write(`[ae-handoff] json: ${outputJsonPath}\n`);
  process.stdout.write(`[ae-handoff] markdown: ${outputMarkdownPath}\n`);
  return { exitCode: 0, handoff };
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  try {
    const result = run(process.argv.slice(2));
    if (result.exitCode !== 0) {
      process.exitCode = result.exitCode;
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`[ae-handoff] ${message}\n`);
    process.exitCode = 1;
  }
}
